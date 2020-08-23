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