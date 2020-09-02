module Ocaml.Utils

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.List
import Data.Vect

export
traverse : (a -> Core b) -> Vect n a -> Core (Vect n b)
traverse f [] = pure []
traverse f (x::xs) = do
    x' <- f x
    xs' <- traverse f xs
    pure $ x' :: xs'


export
for : List a -> (a -> Core b) -> Core (List b)
for [] f = pure []
for (x::xs) f = do
    x' <- f x
    rest <- for xs f
    pure (x' :: rest)

export
for_ : List a -> (a -> Core ()) -> Core ()
for_ [] f = pure ()
for_ (x::xs) f = do
    () <- f x
    for_ xs f


export
binOp : (op : String) -> (a, b : String) -> String
binOp op a b = "(" ++ a ++ " " ++ op ++ " " ++ b ++ ")"

export
fnCall : (fn : String) -> (args : List String) -> String
fnCall fn args = "(" ++ fn ++ " " ++ showSep " " args ++ ")"

export
boolOp : (op : String) -> (a, b : String) -> String
boolOp op a b = fnCall "int_of_bool" [binOp op a b]



export
modFromNamespace : List String -> String
modFromNamespace ns = "Mod_" ++ concat (intersperse "_" $ reverse ns)

export
namespace' : Name -> String
namespace' (NS ns _) = modFromNamespace ns
namespace' _ = "Misc"

public export
flap : List a -> (a -> b) -> List b
flap = flip map
