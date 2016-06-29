{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
-- |
-- This module generates code in the simplified Javascript intermediate representation from Purescript code
--
module Language.PyreScript.CodeGen.Py
  ( module AST
  , module Common
  , moduleToPy
  ) where

import Prelude.Compat

import Control.Arrow ((&&&))
import Control.Monad (replicateM, forM, void)
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.Reader (MonadReader, asks)
import Control.Monad.Supply.Class

import Data.List ((\\), delete, intersect)
import Data.Maybe (isNothing, fromMaybe)
import qualified Data.Foldable as F
import qualified Data.Map as M
import qualified Data.Traversable as T

import Language.PureScript.AST.SourcePos
import qualified Language.PureScript.CodeGen.JS.AST as AST
import qualified Language.PyreScript.CodeGen.Py.Common as Common
import qualified Language.PureScript.CodeGen.JS.Optimizer as Optimizer
import Language.PureScript.CoreFn
import Language.PureScript.Crash
import Language.PureScript.Errors
import Language.PureScript.Names
import Language.PureScript.Options
import Language.PureScript.Traversals (sndM)
import qualified Language.PureScript.Constants as C

import System.FilePath.Posix ((</>))

-- |
-- Generate code in the simplified Javascript intermediate representation for all declarations in a
-- module.
--
moduleToPy
  :: forall m
   . (Monad m, MonadReader Options m, MonadSupply m, MonadError MultipleErrors m)
  => Module Ann
  -> Maybe AST.JS
  -> m [AST.JS]
moduleToPy (Module coms mn imps exps foreigns decls) foreign_ =
  rethrow (addHint (ErrorInModule mn)) $ do
    let usedNames = concatMap getNames decls
    let mnLookup = renameImports usedNames imps
    jsImports <- T.traverse (importToJs mnLookup) . delete (ModuleName [ProperName C.prim]) . (\\ [mn]) $ map snd imps
    let decls' = renameModules mnLookup decls
    jsDecls <- mapM bindToJs decls'
    optimized <- T.traverse (T.traverse Optimizer.optimize) jsDecls
    F.traverse_ (F.traverse_ checkIntegers) optimized
    comments <- not <$> asks optionsNoComments
    let strict = AST.JSRaw Nothing ""
    let header = if comments && not (null coms) then AST.JSComment Nothing coms strict else strict
    let foreign' = [AST.JSVariableIntroduction Nothing "__foreign__" foreign_ | not $ null foreigns || isNothing foreign_]
    let moduleBody = header : foreign' ++ jsImports ++ concat optimized
    let foreignExps = exps `intersect` (fst `map` foreigns)
    let standardExps = exps \\ foreignExps
    let exps' = AST.JSArrayLiteral Nothing $ map (AST.JSVar Nothing . show . Common.identToPy) standardExps
                               ++ map foreignIdent foreignExps
    return $ moduleBody ++ [AST.JSAssignment Nothing (AST.JSVar Nothing "__all__") exps']

  where

  -- |
  -- Extracts all declaration names from a binding group.
  --
  getNames :: Bind Ann -> [Ident]
  getNames (NonRec _ ident _) = [ident]
  getNames (Rec vals) = map (snd . fst) vals

  -- |
  -- Creates alternative names for each module to ensure they don't collide
  -- with declaration names.
  --
  renameImports :: [Ident] -> [(Ann, ModuleName)] -> M.Map ModuleName (Ann, ModuleName)
  renameImports = go M.empty
    where
    go :: M.Map ModuleName (Ann, ModuleName) -> [Ident] -> [(Ann, ModuleName)] -> M.Map ModuleName (Ann, ModuleName)
    go acc used ((ann, mn') : mns') =
      let mni = Ident $ runModuleName mn'
      in if mn' /= mn && mni `elem` used
         then let newName = freshModuleName 1 mn' used
              in go (M.insert mn' (ann, newName) acc) (Ident (runModuleName newName) : used) mns'
         else go (M.insert mn' (ann, mn') acc) (mni : used) mns'
    go acc _ [] = acc

    freshModuleName :: Integer -> ModuleName -> [Ident] -> ModuleName
    freshModuleName i mn'@(ModuleName pns) used =
      let newName = ModuleName $ init pns ++ [ProperName $ runProperName (last pns) ++ "_" ++ show i]
      in if Ident (runModuleName newName) `elem` used
         then freshModuleName (i + 1) mn' used
         else newName

  -- |
  -- Generates Javascript code for a module import, binding the required module
  -- to the alternative
  --
  importToJs :: M.Map ModuleName (Ann, ModuleName) -> ModuleName -> m AST.JS
  importToJs mnLookup mn' = do
    let ((ss, _, _, _), mnSafe) = fromMaybe (internalError "Missing value in mnLookup") $ M.lookup mn' mnLookup
    let moduleBody = AST.JSApp Nothing (AST.JSVar Nothing "require") [AST.JSStringLiteral Nothing (".." </> runModuleName mn')]
    withPos ss $ AST.JSVariableIntroduction Nothing (Common.moduleNameToPy mnSafe) (Just moduleBody)

  -- |
  -- Replaces the `ModuleName`s in the AST so that the generated code refers to
  -- the collision-avoiding renamed module imports.
  --
  renameModules :: M.Map ModuleName (Ann, ModuleName) -> [Bind Ann] -> [Bind Ann]
  renameModules mnLookup binds =
    let (f, _, _) = everywhereOnValues id goExpr goBinder
    in map f binds
    where
    goExpr :: Expr a -> Expr a
    goExpr (Var ann q) = Var ann (renameQual q)
    goExpr e = e
    goBinder :: Binder a -> Binder a
    goBinder (ConstructorBinder ann q1 q2 bs) = ConstructorBinder ann (renameQual q1) (renameQual q2) bs
    goBinder b = b
    renameQual :: Qualified a -> Qualified a
    renameQual (Qualified (Just mn') a) =
      let (_,mnSafe) = fromMaybe (internalError "Missing value in mnLookup") $ M.lookup mn' mnLookup
      in Qualified (Just mnSafe) a
    renameQual q = q

  -- |
  -- Generate code in the simplified Javascript intermediate representation for a declaration
  --
  bindToJs :: Bind Ann -> m [AST.JS]
  bindToJs (NonRec ann ident val) = return <$> nonRecToJS ann ident val
  bindToJs (Rec vals) = forM vals (uncurry . uncurry $ nonRecToJS)

  -- |
  -- Generate code in the simplified Javascript intermediate representation for a single non-recursive
  -- declaration.
  --
  -- The main purpose of this function is to handle code generation for comments.
  --
  nonRecToJS :: Ann -> Ident -> Expr Ann -> m AST.JS
  nonRecToJS a i e@(extractAnn -> (_, com, _, _)) | not (null com) = do
    withoutComment <- asks optionsNoComments
    if withoutComment
       then nonRecToJS a i (modifyAnn removeComments e)
       else AST.JSComment Nothing com <$> nonRecToJS a i (modifyAnn removeComments e)
  nonRecToJS (ss, _, _, _) ident val = do
    js <- valueToJs val
    withPos ss $ AST.JSVariableIntroduction Nothing (Common.identToPy ident) (Just js)

  withPos :: Maybe SourceSpan -> AST.JS -> m AST.JS
  withPos (Just ss) js = do
    withSM <- asks optionsSourceMaps
    return $ if withSM
      then AST.withSourceSpan ss js
      else js
  withPos Nothing js = return js

  -- |
  -- Generate code in the simplified Javascript intermediate representation for a variable based on a
  -- PureScript identifier.
  --
  var :: Ident -> AST.JS
  var = AST.JSVar Nothing . Common.identToPy

  -- |
  -- Generate code in the simplified Javascript intermediate representation for an accessor based on
  -- a PureScript identifier. If the name is not valid in Javascript (symbol based, reserved name) an
  -- indexer is returned.
  --
  accessor :: Ident -> AST.JS -> AST.JS
  accessor (Ident prop) = accessorString prop
  accessor (GenIdent _ _) = internalError "GenIdent in accessor"

  accessorString :: String -> AST.JS -> AST.JS
  accessorString prop | Common.identNeedsEscaping prop = AST.JSIndexer Nothing (AST.JSStringLiteral Nothing prop)
                      | otherwise = AST.JSAccessor Nothing prop

  -- |
  -- Generate code in the simplified Javascript intermediate representation for a value or expression.
  --
  valueToJs :: Expr Ann -> m AST.JS
  valueToJs e =
    let (ss, _, _, _) = extractAnn e in
    withPos ss =<< valueToJs' e

  valueToJs' :: Expr Ann -> m AST.JS
  valueToJs' (Literal (pos, _, _, _) l) =
    maybe id rethrowWithPosition pos $ literalToValueJS l
  valueToJs' (Var (_, _, _, Just (IsConstructor _ [])) name) =
    return $ AST.JSAccessor Nothing "value" $ qualifiedToJS id name
  valueToJs' (Var (_, _, _, Just (IsConstructor _ _)) name) =
    return $ AST.JSAccessor Nothing "create" $ qualifiedToJS id name
  valueToJs' (Accessor _ prop val) =
    accessorString prop <$> valueToJs val
  valueToJs' (ObjectUpdate _ o ps) = do
    obj <- valueToJs o
    sts <- mapM (sndM valueToJs) ps
    extendObj obj sts
  valueToJs' e@(Abs (_, _, _, Just IsTypeClassConstructor) _ _) =
    let args = unAbs e
    in return $ AST.JSFunction Nothing Nothing (map Common.identToPy args) (AST.JSBlock Nothing $ map assign args)
    where
    unAbs :: Expr Ann -> [Ident]
    unAbs (Abs _ arg val) = arg : unAbs val
    unAbs _ = []
    assign :: Ident -> AST.JS
    assign name = AST.JSAssignment Nothing (accessorString (runIdent name) (AST.JSVar Nothing "this"))
                               (var name)
  valueToJs' (Abs _ arg val) = do
    ret <- valueToJs val
    return $ AST.JSFunction Nothing Nothing [Common.identToPy arg] (AST.JSBlock Nothing [AST.JSReturn Nothing ret])
  valueToJs' e@App{} = do
    let (f, args) = unApp e []
    args' <- mapM valueToJs args
    case f of
      Var (_, _, _, Just IsNewtype) _ -> return (head args')
      Var (_, _, _, Just (IsConstructor _ fields)) name | length args == length fields ->
        return $ AST.JSUnary Nothing AST.JSNew $ AST.JSApp Nothing (qualifiedToJS id name) args'
      Var (_, _, _, Just IsTypeClassConstructor) name ->
        return $ AST.JSUnary Nothing AST.JSNew $ AST.JSApp Nothing (qualifiedToJS id name) args'
      _ -> flip (foldl (\fn a -> AST.JSApp Nothing fn [a])) args' <$> valueToJs f
    where
    unApp :: Expr Ann -> [Expr Ann] -> (Expr Ann, [Expr Ann])
    unApp (App _ val arg) args = unApp val (arg : args)
    unApp other args = (other, args)
  valueToJs' (Var (_, _, _, Just IsForeign) qi@(Qualified (Just mn') ident)) =
    return $ if mn' == mn
             then foreignIdent ident
             else varToJs qi
  valueToJs' (Var (_, _, _, Just IsForeign) ident) =
    error $ "Encountered an unqualified reference to a foreign ident " ++ showQualified showIdent ident
  valueToJs' (Var _ ident) = return $ varToJs ident
  valueToJs' (Case (maybeSpan, _, _, _) values binders) = do
    vals <- mapM valueToJs values
    bindersToJs maybeSpan binders vals
  valueToJs' (Let _ ds val) = do
    ds' <- concat <$> mapM bindToJs ds
    ret <- valueToJs val
    return $ AST.JSApp Nothing (AST.JSFunction Nothing Nothing [] (AST.JSBlock Nothing (ds' ++ [AST.JSReturn Nothing ret]))) []
  valueToJs' (Constructor (_, _, _, Just IsNewtype) _ (ProperName ctor) _) =
    return $ AST.JSVariableIntroduction Nothing ctor (Just $
                AST.JSObjectLiteral Nothing [("create",
                  AST.JSFunction Nothing Nothing ["value"]
                    (AST.JSBlock Nothing [AST.JSReturn Nothing $ AST.JSVar Nothing "value"]))])
  valueToJs' (Constructor _ _ (ProperName ctor) []) =
    return $ iife ctor [ AST.JSFunction Nothing (Just ctor) [] (AST.JSBlock Nothing [])
           , AST.JSAssignment Nothing (AST.JSAccessor Nothing "value" (AST.JSVar Nothing ctor))
                (AST.JSUnary Nothing AST.JSNew $ AST.JSApp Nothing (AST.JSVar Nothing ctor) []) ]
  valueToJs' (Constructor _ _ (ProperName ctor) fields) =
    let constructor =
          let body = [ AST.JSAssignment Nothing (AST.JSAccessor Nothing (Common.identToPy f) (AST.JSVar Nothing "this")) (var f) | f <- fields ]
          in AST.JSFunction Nothing (Just ctor) (Common.identToPy `map` fields) (AST.JSBlock Nothing body)
        createFn =
          let body = AST.JSUnary Nothing AST.JSNew $ AST.JSApp Nothing (AST.JSVar Nothing ctor) (var `map` fields)
          in foldr (\f inner -> AST.JSFunction Nothing Nothing [Common.identToPy f] (AST.JSBlock Nothing [AST.JSReturn Nothing inner])) body fields
    in return $ iife ctor [ constructor
                          , AST.JSAssignment Nothing (AST.JSAccessor Nothing "create" (AST.JSVar Nothing ctor)) createFn
                          ]

  iife :: String -> [AST.JS] -> AST.JS
  iife v exprs = AST.JSApp Nothing (AST.JSFunction Nothing Nothing [] (AST.JSBlock Nothing $ exprs ++ [AST.JSReturn Nothing $ AST.JSVar Nothing v])) []

  literalToValueJS :: Literal (Expr Ann) -> m AST.JS
  literalToValueJS (NumericLiteral (Left i)) = return $ AST.JSNumericLiteral Nothing (Left i)
  literalToValueJS (NumericLiteral (Right n)) = return $ AST.JSNumericLiteral Nothing (Right n)
  literalToValueJS (StringLiteral s) = return $ AST.JSStringLiteral Nothing s
  literalToValueJS (CharLiteral c) = return $ AST.JSStringLiteral Nothing [c]
  literalToValueJS (BooleanLiteral b) = return $ AST.JSBooleanLiteral Nothing b
  literalToValueJS (ArrayLiteral xs) = AST.JSArrayLiteral Nothing <$> mapM valueToJs xs
  literalToValueJS (ObjectLiteral ps) = AST.JSObjectLiteral Nothing <$> mapM (sndM valueToJs) ps

  -- |
  -- Shallow copy an object.
  --
  extendObj :: AST.JS -> [(String, AST.JS)] -> m AST.JS
  extendObj obj sts = do
    newObj <- freshName
    key <- freshName
    let
      jsKey = AST.JSVar Nothing key
      jsNewObj = AST.JSVar Nothing newObj
      block = AST.JSBlock Nothing (objAssign:copy:extend ++ [AST.JSReturn Nothing jsNewObj])
      objAssign = AST.JSVariableIntroduction Nothing newObj (Just $ AST.JSObjectLiteral Nothing [])
      copy = AST.JSForIn Nothing key obj $ AST.JSBlock Nothing [AST.JSIfElse Nothing cond assign Nothing]
      cond = AST.JSApp Nothing (AST.JSAccessor Nothing "hasOwnProperty" obj) [jsKey]
      assign = AST.JSBlock Nothing [AST.JSAssignment Nothing (AST.JSIndexer Nothing jsKey jsNewObj) (AST.JSIndexer Nothing jsKey obj)]
      stToAssign (s, js) = AST.JSAssignment Nothing (AST.JSAccessor Nothing s jsNewObj) js
      extend = map stToAssign sts
    return $ AST.JSApp Nothing (AST.JSFunction Nothing Nothing [] block) []

  -- |
  -- Generate code in the simplified Javascript intermediate representation for a reference to a
  -- variable.
  --
  varToJs :: Qualified Ident -> AST.JS
  varToJs (Qualified Nothing ident) = var ident
  varToJs qual = qualifiedToJS id qual

  -- |
  -- Generate code in the simplified Javascript intermediate representation for a reference to a
  -- variable that may have a qualified name.
  --
  qualifiedToJS :: (a -> Ident) -> Qualified a -> AST.JS
  qualifiedToJS f (Qualified (Just (ModuleName [ProperName mn'])) a) | mn' == C.prim = AST.JSVar Nothing . runIdent $ f a
  qualifiedToJS f (Qualified (Just mn') a) | mn /= mn' = accessor (f a) (AST.JSVar Nothing (Common.moduleNameToPy mn'))
  qualifiedToJS f (Qualified _ a) = AST.JSVar Nothing $ Common.identToPy (f a)

  foreignIdent :: Ident -> AST.JS
  foreignIdent ident = accessorString (runIdent ident) (AST.JSVar Nothing "$foreign")

  -- |
  -- Generate code in the simplified Javascript intermediate representation for pattern match binders
  -- and guards.
  --
  bindersToJs :: Maybe SourceSpan -> [CaseAlternative Ann] -> [AST.JS] -> m AST.JS
  bindersToJs maybeSpan binders vals = do
    valNames <- replicateM (length vals) freshName
    let assignments = zipWith (AST.JSVariableIntroduction Nothing) valNames (map Just vals)
    jss <- forM binders $ \(CaseAlternative bs result) -> do
      ret <- guardsToJs result
      go valNames ret bs
    return $ AST.JSApp Nothing (AST.JSFunction Nothing Nothing [] (AST.JSBlock Nothing (assignments ++ concat jss ++ [AST.JSThrow Nothing $ failedPatternError valNames])))
                   []
    where
      go :: [String] -> [AST.JS] -> [Binder Ann] -> m [AST.JS]
      go _ done [] = return done
      go (v:vs) done' (b:bs) = do
        done'' <- go vs done' bs
        binderToJs v done'' b
      go _ _ _ = internalError "Invalid arguments to bindersToJs"

      failedPatternError :: [String] -> AST.JS
      failedPatternError names = AST.JSUnary Nothing AST.JSNew $ AST.JSApp Nothing (AST.JSVar Nothing "Error") [AST.JSBinary Nothing AST.Add (AST.JSStringLiteral Nothing failedPatternMessage) (AST.JSArrayLiteral Nothing $ zipWith valueError names vals)]

      failedPatternMessage :: String
      failedPatternMessage = "Failed pattern match" ++ maybe "" (((" at " ++ runModuleName mn ++ " ") ++) . displayStartEndPos) maybeSpan ++ ": "

      valueError :: String -> AST.JS -> AST.JS
      valueError _ l@(AST.JSNumericLiteral _ _) = l
      valueError _ l@(AST.JSStringLiteral _ _)  = l
      valueError _ l@(AST.JSBooleanLiteral _ _) = l
      valueError s _                            = AST.JSAccessor Nothing "name" . AST.JSAccessor Nothing "constructor" $ AST.JSVar Nothing s

      guardsToJs :: Either [(Guard Ann, Expr Ann)] (Expr Ann) -> m [AST.JS]
      guardsToJs (Left gs) = forM gs $ \(cond, val) -> do
        cond' <- valueToJs cond
        done  <- valueToJs val
        return $ AST.JSIfElse Nothing cond' (AST.JSBlock Nothing [AST.JSReturn Nothing done]) Nothing
      guardsToJs (Right v) = return . AST.JSReturn Nothing <$> valueToJs v

  binderToJs :: String -> [AST.JS] -> Binder Ann -> m [AST.JS]
  binderToJs s done binder =
    let (ss, _, _, _) = extractBinderAnn binder in
    traverse (withPos ss) =<< binderToJs' s done binder

  -- |
  -- Generate code in the simplified Javascript intermediate representation for a pattern match
  -- binder.
  --
  binderToJs' :: String -> [AST.JS] -> Binder Ann -> m [AST.JS]
  binderToJs' _ done (NullBinder{}) = return done
  binderToJs' varName done (LiteralBinder _ l) =
    literalToBinderJS varName done l
  binderToJs' varName done (VarBinder _ ident) =
    return (AST.JSVariableIntroduction Nothing (Common.identToPy ident) (Just (AST.JSVar Nothing varName)) : done)
  binderToJs' varName done (ConstructorBinder (_, _, _, Just IsNewtype) _ _ [b]) =
    binderToJs varName done b
  binderToJs' varName done (ConstructorBinder (_, _, _, Just (IsConstructor ctorType fields)) _ ctor bs) = do
    js <- go (zip fields bs) done
    return $ case ctorType of
      ProductType -> js
      SumType ->
        [AST.JSIfElse Nothing (AST.JSInstanceOf Nothing (AST.JSVar Nothing varName) (qualifiedToJS (Ident . runProperName) ctor))
                  (AST.JSBlock Nothing js)
                  Nothing]
    where
    go :: [(Ident, Binder Ann)] -> [AST.JS] -> m [AST.JS]
    go [] done' = return done'
    go ((field, binder) : remain) done' = do
      argVar <- freshName
      done'' <- go remain done'
      js <- binderToJs argVar done'' binder
      return (AST.JSVariableIntroduction Nothing argVar (Just (AST.JSAccessor Nothing (Common.identToPy field) (AST.JSVar Nothing varName))) : js)
  binderToJs' _ _ ConstructorBinder{} =
    internalError "binderToJs: Invalid ConstructorBinder in binderToJs"
  binderToJs' varName done (NamedBinder _ ident binder) = do
    js <- binderToJs varName done binder
    return (AST.JSVariableIntroduction Nothing (Common.identToPy ident) (Just (AST.JSVar Nothing varName)) : js)

  literalToBinderJS :: String -> [AST.JS] -> Literal (Binder Ann) -> m [AST.JS]
  literalToBinderJS varName done (NumericLiteral num) =
    return [AST.JSIfElse Nothing (AST.JSBinary Nothing AST.EqualTo (AST.JSVar Nothing varName) (AST.JSNumericLiteral Nothing num)) (AST.JSBlock Nothing done) Nothing]
  literalToBinderJS varName done (CharLiteral c) =
    return [AST.JSIfElse Nothing (AST.JSBinary Nothing AST.EqualTo (AST.JSVar Nothing varName) (AST.JSStringLiteral Nothing [c])) (AST.JSBlock Nothing done) Nothing]
  literalToBinderJS varName done (StringLiteral str) =
    return [AST.JSIfElse Nothing (AST.JSBinary Nothing AST.EqualTo (AST.JSVar Nothing varName) (AST.JSStringLiteral Nothing str)) (AST.JSBlock Nothing done) Nothing]
  literalToBinderJS varName done (BooleanLiteral True) =
    return [AST.JSIfElse Nothing (AST.JSVar Nothing varName) (AST.JSBlock Nothing done) Nothing]
  literalToBinderJS varName done (BooleanLiteral False) =
    return [AST.JSIfElse Nothing (AST.JSUnary Nothing AST.Not (AST.JSVar Nothing varName)) (AST.JSBlock Nothing done) Nothing]
  literalToBinderJS varName done (ObjectLiteral bs) = go done bs
    where
    go :: [AST.JS] -> [(String, Binder Ann)] -> m [AST.JS]
    go done' [] = return done'
    go done' ((prop, binder):bs') = do
      propVar <- freshName
      done'' <- go done' bs'
      js <- binderToJs propVar done'' binder
      return (AST.JSVariableIntroduction Nothing propVar (Just (accessorString prop (AST.JSVar Nothing varName))) : js)
  literalToBinderJS varName done (ArrayLiteral bs) = do
    js <- go done 0 bs
    return [AST.JSIfElse Nothing (AST.JSBinary Nothing AST.EqualTo (AST.JSAccessor Nothing "length" (AST.JSVar Nothing varName)) (AST.JSNumericLiteral Nothing (Left (fromIntegral $ length bs)))) (AST.JSBlock Nothing js) Nothing]
    where
    go :: [AST.JS] -> Integer -> [Binder Ann] -> m [AST.JS]
    go done' _ [] = return done'
    go done' index (binder:bs') = do
      elVar <- freshName
      done'' <- go done' (index + 1) bs'
      js <- binderToJs elVar done'' binder
      return (AST.JSVariableIntroduction Nothing elVar (Just (AST.JSIndexer Nothing (AST.JSNumericLiteral Nothing (Left index)) (AST.JSVar Nothing varName))) : js)

  -- Check that all integers fall within the valid int range for JavaScript.
  checkIntegers :: AST.JS -> m ()
  checkIntegers = void . AST.everywhereOnJSTopDownM go
    where
    go :: AST.JS -> m AST.JS
    go (AST.JSUnary _ AST.Negate (AST.JSNumericLiteral ss (Left i))) =
      -- Move the negation inside the literal; since this is a top-down
      -- traversal doing this replacement will stop the next case from raising
      -- the error when attempting to use -2147483648, as if left unrewritten
      -- the value is `AST.JSUnary Negate (AST.JSNumericLiteral (Left 2147483648))`, and
      -- 2147483648 is larger than the maximum allowed int.
      return $ AST.JSNumericLiteral ss (Left (-i))
    go js@(AST.JSNumericLiteral _ (Left i)) =
      let minInt = -2147483648
          maxInt = 2147483647
      in if i < minInt || i > maxInt
         then throwError . errorMessage $ IntOutOfRange i "JavaScript" minInt maxInt
         else return js
    go other = return other
