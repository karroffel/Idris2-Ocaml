module Ocaml.Foreign

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.NameMap
import Data.Vect
import Data.List

import Ocaml.DefInfo
import Ocaml.Expr

implNames : List (String, String)
implNames = [
    ("Prelude.IO.prim__putStr", "idr2_print_string")
]

export
foreignFun : Name -> String
foreignFun name = case lookup (show name) implNames of
    Just name => name
    Nothing => "raise (Idris2_Exception \"Unsupported foreign function " ++ show name ++ "\")"