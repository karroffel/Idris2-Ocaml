module Ocaml.Utils

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.Vect

export
traverse : (a -> Core b) -> Vect n a -> Core (Vect n b)
traverse f [] = pure []
traverse f (x::xs) = do
    x' <- f x
    xs' <- traverse f xs
    pure $ x' :: xs'

export
binOp : (op : String) -> (a, b : String) -> String
binOp op a b = "(" ++ a ++ " " ++ op ++ " " ++ b ++ ")"

export
fnCall : (fn : String) -> (args : List String) -> String
fnCall fn args = "(" ++ fn ++ " " ++ showSep " " args ++ ")"

export
boolOp : (op : String) -> (a, b : String) -> String
boolOp op a b = fnCall "int_of_bool" [binOp op a b]
            