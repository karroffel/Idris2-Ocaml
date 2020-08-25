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

import Ocaml.DefInfo

implNames : List (String, String)
implNames = [
    ("Prelude.IO.prim__putStr", "idr2_print_string"),
    ("Prelude.IO.prim__getStr", "idr2_get_string"),
    ("System.prim__system", "idr2_system")
    {-
    ("Prelude.IO.prim__getString", "as_string"), -- Ptr -> String
    ("PrimIO.prim__nullAnyPtr", "idr2_is_null"), -- [] -> Ptr
    ("System.File.prim__open", "idr2_sys_file_open"), -- [String, String, %World] -> IORes Ptr
    ("System.File.prim__close", "idr2_sys_file_close"), -- [Ptr, %World] -> IORes Unit
    ("System.File.prim__readLine", "idr2_sys_file_read_line") -- [Ptr, %World] -> IORes Ptr
    
    -- System.File.prim__fileErrno : [%World] -> IORes Int
    -- System.File.prim__open : [String, String, %World] -> IORes Ptr
    -- System.File.prim__readLine : [Ptr, %World] -> IORes Ptr

    -}
]

export
foreignFun : Name -> List CFType -> CFType -> String
foreignFun name args ret = case lookup (show name) implNames of
    Just name => name
    Nothing => "raise (Idris2_Exception \"Unsupported foreign function " ++ show name ++ " : " ++ show args ++ " -> " ++ show ret ++ "\")"