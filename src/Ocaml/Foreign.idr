||| Foreign function definitions
|||
||| These are hardcoded and matched against the name for now.
||| If this backend ever gets included in the compiler then all those
||| mappings can be added to the functions in `libs/` instead.
module Ocaml.Foreign

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.NameMap
import Data.Vect
import Data.List
import Data.List1
import Data.Strings

import Ocaml.DefInfo

implNames : List (String, String)
implNames = [
    ("Data.Strings.fastConcat", "string_fast_concat")
]

ccLibFun : List String -> Maybe String
ccLibFun [] = Nothing
ccLibFun (cc :: ccs) =
  if substr 0 3 cc == "ML:"
    then Just (substr 3 (length cc) cc)
    else if substr 0 2 cc == "C:"
        then case split (== ',') (substr 2 (length cc) cc) of
          [fn, libn] => Just ("OcamlRts.C.Lib_" ++ rmSpaces libn ++ "." ++ fn)
          _ => ccLibFun ccs  -- something strange -> skip
        else ccLibFun ccs  -- search further
  where
    rmSpaces : String -> String
    rmSpaces = pack . filter (/= ' ') . unpack



export
foreignFun : Name -> List String -> List CFType -> CFType -> String
foreignFun name ccs args ret =
    case ccLibFun ccs of
    Just name => name
    Nothing => case lookup (show name) implNames of
        Just fn => fn
        Nothing => "raise (Idris2_Exception \"Unsupported foreign function " ++ show name ++ " : " ++ show args ++ " -> " ++ show ret ++ "\")"