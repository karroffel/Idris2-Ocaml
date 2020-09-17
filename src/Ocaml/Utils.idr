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
parens : String -> String
parens s = "(" ++ s ++ ")"

export
binOp : (op : String) -> (a, b : String) -> String
binOp op a b = parens $ a ++ " " ++ op ++ " " ++ b

export
fnCall : (fn : String) -> (args : List String) -> String
fnCall fn args = parens $ fn ++ " " ++ showSep " " args

export
boolOp : (op : String) -> (a, b : String) -> String
boolOp op a b = fnCall "int_of_bool" [binOp op a b]

export
mlRepr : String -> String
mlRepr s = fnCall "Obj.repr" [s]




export
namespace' : Name -> String
namespace' (NS ns _) = "Mod_" ++ showNSWithSep "_" ns
namespace' _ = "Misc"


public export
flap : List a -> (a -> b) -> List b
flap = flip map



export
asInt : String -> String
asInt s = fnCall "as_int" [s]

export
asBint : String -> String
asBint s = fnCall "as_bint" [s]

export
asBits8 : String -> String
asBits8 s = fnCall "as_bits8" [s]

export
asBits16 : String -> String
asBits16 s = fnCall "as_bits16" [s]

export
asBits32 : String -> String
asBits32 s = fnCall "as_bits32" [s]

export
asBits64 : String -> String
asBits64 s = fnCall "as_bits64" [s]

export
asString : String -> String
asString s = fnCall "as_string" [s]

export
asChar : String -> String
asChar s = fnCall "as_char" [s]

export
asDouble : String -> String
asDouble s = fnCall "as_double" [s]
