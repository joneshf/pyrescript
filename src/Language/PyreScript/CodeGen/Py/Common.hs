-- |
-- Common code generation utility functions
--
module Language.PyreScript.CodeGen.Py.Common
  ( identNeedsEscaping
  , identToPy
  , moduleNameToPy
  ) where

import Prelude.Compat

import Data.Char
import Data.List (intercalate)

import Language.PureScript.Crash
import Language.PureScript.Names

moduleNameToPy :: ModuleName -> String
moduleNameToPy (ModuleName pns) =
  let name = intercalate "_" (runProperName `map` pns)
  in if nameIsPyBuiltIn name then "__" ++ name ++ "__" else name

-- |
-- Convert an Ident into a valid Javascript identifier:
--
--  * Alphanumeric characters are kept unmodified.
--
--  * Reserved javascript identifiers are prefixed with '$$'.
--
--  * Symbols are prefixed with '$' followed by a symbol name or their ordinal value.
--
identToPy :: Ident -> String
identToPy (Ident name)
  | nameIsPyReserved name || nameIsPyBuiltIn name = "__" ++ name ++ "__"
  | otherwise = concatMap identCharToString name
identToPy (GenIdent _ _) = internalError "GenIdent in identToPy"

-- |
-- Test if a string is ayvalid Py identifier without escaping.
--
identNeedsEscaping :: String -> Bool
identNeedsEscaping s = s /= identToPy (Ident s)

-- |
-- Attempts to find a human-readable name for a symbol, if none has been specified returns the
-- ordinal value.
--
identCharToString :: Char -> String
identCharToString c | isAlphaNum c = [c]
identCharToString '_' = "_"
identCharToString '.' = "__dot__"
identCharToString '$' = "__dollar__"
identCharToString '~' = "__tilde__"
identCharToString '=' = "__eq__"
identCharToString '<' = "__less__"
identCharToString '>' = "__greater__"
identCharToString '!' = "__bang__"
identCharToString '#' = "__hash__"
identCharToString '%' = "__percent__"
identCharToString '^' = "__up__"
identCharToString '&' = "__amp__"
identCharToString '|' = "__bar__"
identCharToString '*' = "__times__"
identCharToString '/' = "__div__"
identCharToString '+' = "__plus__"
identCharToString '-' = "__minus__"
identCharToString ':' = "__colon__"
identCharToString '\\' = "__bslash__"
identCharToString '?' = "__qmark__"
identCharToString '@' = "__at__"
identCharToString '\'' = "__prime__"
identCharToString c = "__" ++ show (ord c) ++ "__"

-- |
-- Checks whether an identifier name is reserved in Javascript.
--
nameIsPyReserved :: String -> Bool
nameIsPyReserved name =
  name `elem` pyAnyReserved

-- |
-- Checks whether a name matches a built-in value in Javascript.
--
nameIsPyBuiltIn :: String -> Bool
nameIsPyBuiltIn name =
  name `elem`
    [ "arguments"
    , "Array"
    , "ArrayBuffer"
    , "Boolean"
    , "DataView"
    , "Date"
    , "decodeURI"
    , "decodeURIComponent"
    , "encodeURI"
    , "encodeURIComponent"
    , "Error"
    , "escape"
    , "eval"
    , "EvalError"
    , "Float32Array"
    , "Float64Array"
    , "Function"
    , "Infinity"
    , "Int16Array"
    , "Int32Array"
    , "Int8Array"
    , "Intl"
    , "isFinite"
    , "isNaN"
    , "JSON"
    , "Map"
    , "Math"
    , "NaN"
    , "Number"
    , "Object"
    , "parseFloat"
    , "parseInt"
    , "Promise"
    , "Proxy"
    , "RangeError"
    , "ReferenceError"
    , "Reflect"
    , "RegExp"
    , "Set"
    , "SIMD"
    , "String"
    , "Symbol"
    , "SyntaxError"
    , "TypeError"
    , "Uint16Array"
    , "Uint32Array"
    , "Uint8Array"
    , "Uint8ClampedArray"
    , "undefined"
    , "unescape"
    , "URIError"
    , "WeakMap"
    , "WeakSet"
    ]

pyAnyReserved :: [String]
pyAnyReserved =
  concat
    [ pyKeywords
    , pyLiterals
    ]

pyKeywords :: [String]
pyKeywords =
  [ "and"
  , "as"
  , "assert"
  , "break"
  , "class"
  , "continue"
  , "def"
  , "del"
  , "elif"
  , "else"
  , "except"
  , "exec"
  , "finally"
  , "for"
  , "from"
  , "global"
  , "if"
  , "import"
  , "in"
  , "is"
  , "lambda"
  , "not"
  , "or"
  , "pass"
  , "print"
  , "raise"
  , "return"
  , "try"
  , "while"
  , "with"
  , "yield"
  ]

pyLiterals :: [String]
pyLiterals =
  [ "None"
  , "True"
  , "False"
  ]
