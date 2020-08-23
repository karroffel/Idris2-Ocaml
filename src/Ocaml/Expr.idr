module Ocaml.Expr

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.List
import Data.Maybe
import Data.NameMap
import Data.Vect

import Utils.Hex

import Ocaml.DefInfo
import Ocaml.Utils


ocamlKeywords : List String
ocamlKeywords = [
    "and", "as", "asr", "assert", "begin", "class",
    "constraint", "do", "done", "downto", "else", "end",
    "exception", "external", "false", "for", "fun", "function",
    "functor", "if", "in", "include", "inherit", "initializer", "land",
    "lazy", "let", "lor", "lsl", "lsr", "lxor", "match", "method",
    "mod", "module", "mutable", "new", "nonrec", "object", "of", "open",
    -- "open!", This should not be a valid Idris identifier
    "or", "private", "rec", "sig", "struct", "then", "to", "true",
    "try", "type", "val", "virtual", "when", "while", "with"
]

export
mlIdent : String -> String
mlIdent s =
    if s `elem` ocamlKeywords
        then s ++ "_'"
        else concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c
                  then cast c
                  else "_" ++ the (String) (asHex (cast {to=Int} c)) ++ "_"

export
mlName : Name -> String
mlName (NS xs x) = showSep "'" (reverse xs) ++ "_" ++ mlName x
mlName (UN x) = mlIdent x
mlName (MN x y) = mlIdent x ++ "_" ++ show y
mlName (PV x y) = "pat__" ++ mlName x ++ "_" ++ show y
mlName (DN x y) = mlName y
mlName (Nested (i, x) n) = "n__" ++ show i ++ "_" ++ show x ++ "_" ++ mlName n
mlName (CaseBlock x y) = "case__" ++ mlIdent x ++ "_" ++ show y
mlName (WithBlock x y) = "with__" ++ mlIdent x ++ "_" ++ show y
mlName (Resolved x) = "fn__" ++ show x






public export
record MLExpr where
    constructor MkMLExpr
    source : String
    type : SType

public export
empty : MLExpr
empty = MkMLExpr "" SOpaque

||| The name of the OCaml function that will cast an expression to a type
hintFn : SType -> String
hintFn SErased = "hint_erased"
hintFn SInt = "hint_int"
hintFn SInteger = "hint_bint"
hintFn SBits8 = "hint_bits8"
hintFn SBits16 = "hint_bits16"
hintFn SBits32 = "hint_bits32"
hintFn SBits64 = "hint_bits64"
hintFn SString = "hint_string"
hintFn SChar = "hint_char"
hintFn SDouble = "hint_double"
hintFn SWorld = "hint_world"
hintFn SOpaque = "hint_opaque"

export
ocamlTypeName : SType -> String
ocamlTypeName SErased = "unit"
ocamlTypeName SInt = "int"
ocamlTypeName SInteger = "int64"
ocamlTypeName SBits8 = "int32"
ocamlTypeName SBits16 = "int32"
ocamlTypeName SBits32 = "int32"
ocamlTypeName SBits64 = "int64"
ocamlTypeName SString = "string"
ocamlTypeName SChar = "char"
ocamlTypeName SDouble = "float"
ocamlTypeName SWorld = "unit"
ocamlTypeName SOpaque = "idr2_opaque"

||| The name of the OCaml function that will cast an expression to a type
castFn : SType -> String
castFn SErased = "as_erased"
castFn SInt = "as_int"
castFn SInteger = "as_bint"
castFn SBits8 = "as_bits8"
castFn SBits16 = "as_bits16"
castFn SBits32 = "as_bits32"
castFn SBits64 = "as_bits64"
castFn SString = "as_string"
castFn SChar = "as_char"
castFn SDouble = "as_double"
castFn SWorld = "as_world"
castFn SOpaque = "as_opaque"

||| The name of the OCaml function that casts an expression to a type *if* the
||| cast is needed
maybeCastFn : (from, to : SType) -> Maybe String
maybeCastFn from to = if from == to then Nothing else Just (castFn to)




mlPrimVal : Constant -> Core MLExpr
mlPrimVal (I x) = pure $ MkMLExpr (show x) SInt
mlPrimVal (BI x) = pure $ MkMLExpr (show x ++ "L") SInteger
mlPrimVal (B8 x) = pure $ MkMLExpr (show x ++ "l") SBits8
mlPrimVal (B16 x) = pure $ MkMLExpr (show x ++ "l") SBits16
mlPrimVal (B32 x) = pure $ MkMLExpr (show x ++ "l") SBits32
mlPrimVal (B64 x) = pure $ MkMLExpr (show x ++ "L") SBits64
mlPrimVal (Str x) = pure $ MkMLExpr (show x) SString
mlPrimVal (Ch x) = pure $ MkMLExpr (show x) SChar
mlPrimVal (Db x) = pure $ MkMLExpr (show x) SDouble
mlPrimVal WorldVal = pure $ MkMLExpr "()" SWorld
mlPrimVal val = throw . InternalError $ "Unsupported primitive value: " ++ show val

binOp : (op : String) -> (a, b : String) -> String
binOp op a b = "(" ++ a ++ " " ++ op ++ " " ++ b ++ ")"

fnCall : (fn : String) -> (args : List String) -> String
fnCall fn args = "(" ++ fn ++ " " ++ showSep " " args ++ ")"

record PrimFnRes (arity : Nat) where
    constructor MkPrimFnRes
    argTypes : Vect arity SType
    retType : SType
    printer : Vect arity String -> String

binaryPrimFn : {arity : Nat} -> SType -> (Vect arity String -> String) -> Core (PrimFnRes arity)
binaryPrimFn ty fn = pure $ MkPrimFnRes (replicate arity ty) ty fn

mlPrimFn : PrimFn arity -> Vect arity NamedCExp -> Core (PrimFnRes arity)
mlPrimFn (Add IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "+" a b
mlPrimFn (Add IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Int64.add" [a, b]
mlPrimFn (Add Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => fnCall "Int32.add" [a, b]
mlPrimFn (Add Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => fnCall "Int32.add" [a, b]
mlPrimFn (Add Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => fnCall "Int32.add" [a, b]
mlPrimFn (Add Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.add" [a, b]
mlPrimFn (Add DoubleType) [a, b] = binaryPrimFn SDouble $ \[a, b] => binOp "+." a b
mlPrimFn (Sub IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "-" a b
mlPrimFn (Sub IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Int64.sub" [a, b]
mlPrimFn (Sub Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => fnCall "Int32.sub" [a, b]
mlPrimFn (Sub Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => fnCall "Int32.sub" [a, b]
mlPrimFn (Sub Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => fnCall "Int32.sub" [a, b]
mlPrimFn (Sub Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.sub" [a, b]
mlPrimFn (Sub DoubleType) [a, b] = binaryPrimFn SDouble $ \[a, b] => binOp "-." a b
mlPrimFn (Mul IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "*" a b
mlPrimFn (Mul IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Int64.mul" [a, b]
mlPrimFn (Mul Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => fnCall "Int32.mul" [a, b]
mlPrimFn (Mul Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => fnCall "Int32.mul" [a, b]
mlPrimFn (Mul Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => fnCall "Int32.mul" [a, b]
mlPrimFn (Mul Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.mul" [a, b]
mlPrimFn (Mul DoubleType) [a, b] = binaryPrimFn SDouble $ \[a, b] => binOp "*." a b
mlPrimFn (Div IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "/" a b
mlPrimFn (Div IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Int64.div" [a, b]
mlPrimFn (Div Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => fnCall "Int32.unsigned_div" [a, b]
mlPrimFn (Div Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => fnCall "Int32.unsigned_div" [a, b]
mlPrimFn (Div Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => fnCall "Int32.unsigned_div" [a, b]
mlPrimFn (Div Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.unsigned_div" [a, b]
mlPrimFn (Div DoubleType) [a, b] = binaryPrimFn SDouble $ \[a, b] => binOp "/." a b
mlPrimFn (Mod IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "mod" a b
mlPrimFn (Mod IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Int64.rem" [a, b]
mlPrimFn (Mod Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => fnCall "Int32.unsigned_rem" [a, b]
mlPrimFn (Mod Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => fnCall "Int32.unsigned_rem" [a, b]
mlPrimFn (Mod Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => fnCall "Int32.unsigned_rem" [a, b]
mlPrimFn (Mod Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.unsigned_rem" [a, b]
mlPrimFn (Neg IntType) [a] = pure $ MkPrimFnRes [SInt] SInt $ \[a] => fnCall "-" [a]
mlPrimFn (Neg IntegerType) [a] = pure $ MkPrimFnRes [SInteger] SInteger $ \[a] => fnCall "Int64.neg" [a]
mlPrimFn (Neg DoubleType) [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "-." [a]
mlPrimFn (ShiftL IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "lsl" a b
mlPrimFn (ShiftL IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Int64.shift_left" [a, fnCall "Int64.to_int" [b]]
mlPrimFn (ShiftL Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => fnCall "Int32.shift_left" [a, fnCall "Int32.to_int" [b]]
mlPrimFn (ShiftL Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => fnCall "Int32.shift_left" [a, fnCall "Int32.to_int" [b]]
mlPrimFn (ShiftL Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => fnCall "Int32.shift_left" [a, fnCall "Int32.to_int" [b]]
mlPrimFn (ShiftL Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.shift_left" [a, fnCall "Int64.to_int" [b]]
mlPrimFn (ShiftR IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "lsr" a b
mlPrimFn (ShiftR IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Int64.shift_right" [a, fnCall "Int64.to_int" [b]]
mlPrimFn (ShiftR Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => fnCall "Int32.shift_right" [a, fnCall "Int32.to_int" [b]]
mlPrimFn (ShiftR Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => fnCall "Int32.shift_right" [a, fnCall "Int32.to_int" [b]]
mlPrimFn (ShiftR Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => fnCall "Int32.shift_right" [a, fnCall "Int32.to_int" [b]]
mlPrimFn (ShiftR Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.shift_right" [a, fnCall "Int64.to_int" [b]]
mlPrimFn (BAnd ty) args = ?mlPrimFn_rhs_9
mlPrimFn (BOr ty) args = ?mlPrimFn_rhs_10
mlPrimFn (BXOr ty) args = ?mlPrimFn_rhs_11
mlPrimFn (LT ty) args = ?mlPrimFn_rhs_12
mlPrimFn (LTE ty) args = ?mlPrimFn_rhs_13
mlPrimFn (EQ ty) args = ?mlPrimFn_rhs_14
mlPrimFn (GTE ty) args = ?mlPrimFn_rhs_15
mlPrimFn (GT ty) args = ?mlPrimFn_rhs_16
mlPrimFn StrLength args = ?mlPrimFn_rhs_17
mlPrimFn StrHead args = ?mlPrimFn_rhs_18
mlPrimFn StrTail args = ?mlPrimFn_rhs_19
mlPrimFn StrIndex args = ?mlPrimFn_rhs_20
mlPrimFn StrCons args = ?mlPrimFn_rhs_21
mlPrimFn StrAppend args = ?mlPrimFn_rhs_22
mlPrimFn StrReverse args = ?mlPrimFn_rhs_23
mlPrimFn StrSubstr args = ?mlPrimFn_rhs_24
mlPrimFn DoubleExp args = ?mlPrimFn_rhs_25
mlPrimFn DoubleLog args = ?mlPrimFn_rhs_26
mlPrimFn DoubleSin args = ?mlPrimFn_rhs_27
mlPrimFn DoubleCos args = ?mlPrimFn_rhs_28
mlPrimFn DoubleTan args = ?mlPrimFn_rhs_29
mlPrimFn DoubleASin args = ?mlPrimFn_rhs_30
mlPrimFn DoubleACos args = ?mlPrimFn_rhs_31
mlPrimFn DoubleATan args = ?mlPrimFn_rhs_32
mlPrimFn DoubleSqrt args = ?mlPrimFn_rhs_33
mlPrimFn DoubleFloor args = ?mlPrimFn_rhs_34
mlPrimFn DoubleCeiling args = ?mlPrimFn_rhs_35
mlPrimFn BelieveMe args = ?mlPrimFn_rhs_37
mlPrimFn Crash args = ?mlPrimFn_rhs_38
-- to Int
mlPrimFn (Cast IntegerType IntType) [a] = pure $ MkPrimFnRes [SInteger] SInt $ \[a] => fnCall "Int64.to_int" [a]
mlPrimFn (Cast Bits8Type IntType) [a] = pure $ MkPrimFnRes [SBits8] SInt $ \[a] => fnCall "Int32.to_int" [a]
mlPrimFn (Cast Bits16Type IntType) [a] = pure $ MkPrimFnRes [SBits16] SInt $ \[a] => fnCall "Int32.to_int" [a]
mlPrimFn (Cast Bits32Type IntType) [a] = pure $ MkPrimFnRes [SBits32] SInt $ \[a] => fnCall "Int32.to_int" [a]
mlPrimFn (Cast DoubleType IntType) [a] = pure $ MkPrimFnRes [SDouble] SInt $ \[a] => fnCall "int_of_float" [a]
mlPrimFn (Cast StringType IntType) [a] = pure $ MkPrimFnRes [SString] SInt $ \[a] => fnCall "int_of_string" [a]
mlPrimFn (Cast CharType IntType) [a] = pure $ MkPrimFnRes [SChar] SInt $ \[a] => fnCall "int_of_char" [a]
-- to Integer
mlPrimFn (Cast IntType IntegerType) [a] = pure $ MkPrimFnRes [SInt] SInteger $ \[a] => fnCall "Int64.of_int" [a]
mlPrimFn (Cast Bits8Type IntegerType) [a] = pure $ MkPrimFnRes [SBits8] SInteger $ \[a] => fnCall "Int64.of_int32" [a]
mlPrimFn (Cast Bits16Type IntegerType) [a] = pure $ MkPrimFnRes [SBits16] SInteger $ \[a] => fnCall "Int64.of_int32" [a]
mlPrimFn (Cast Bits32Type IntegerType) [a] = pure $ MkPrimFnRes [SBits32] SInteger $ \[a] => fnCall "Int64.of_int32" [a]
mlPrimFn (Cast Bits64Type IntegerType) [a] = pure $ MkPrimFnRes [SBits64] SInteger $ \[a] => a
mlPrimFn (Cast DoubleType IntegerType) [a] = pure $ MkPrimFnRes [SDouble] SInteger $ \[a] => fnCall "Int64.of_float" [a]
mlPrimFn (Cast CharType IntegerType) [a] = pure $ MkPrimFnRes [SChar] SInteger $ \[a] => fnCall "Int64.of_int" [fnCall "int_of_char" [a]]
mlPrimFn (Cast StringType IntegerType) [a] = pure $ MkPrimFnRes [SString] SInteger $ \[a] => fnCall "Int64.of_string" [a]
-- to Bits8
mlPrimFn (Cast IntType Bits8Type) [a] = pure $ MkPrimFnRes [SInt] SBits8 $ \[a] => fnCall "Int32.of_int" [a]
mlPrimFn (Cast IntegerType Bits8Type) [a] = pure $ MkPrimFnRes [SInteger] SBits8 $ \[a] => fnCall "Int64.to_int32" [a]
mlPrimFn (Cast Bits16Type Bits8Type) [a] = pure $ MkPrimFnRes [SBits16] SBits8 $ \[a] => a -- TODO handle overflow
mlPrimFn (Cast Bits32Type Bits8Type) [a] = pure $ MkPrimFnRes [SBits32] SBits8 $ \[a] => a -- TODO handle overflow
mlPrimFn (Cast Bits64Type Bits8Type) [a] = pure $ MkPrimFnRes [SBits64] SBits8 $ \[a] => fnCall "Int64.to_int32" [a]
-- to Bits16
mlPrimFn (Cast IntType Bits16Type) [a] = pure $ MkPrimFnRes [SInt] SBits16 $ \[a] => fnCall "Int32.of_int" [a]
mlPrimFn (Cast IntegerType Bits16Type) [a] = pure $ MkPrimFnRes [SInteger] SBits16 $ \[a] => fnCall "Int64.to_int32" [a]
mlPrimFn (Cast Bits8Type Bits16Type) [a] = pure $ MkPrimFnRes [SBits8] SBits16 $ \[a] => a
mlPrimFn (Cast Bits32Type Bits16Type) [a] = pure $ MkPrimFnRes [SBits32] SBits16 $ \[a] => a -- TODO handle overflow
mlPrimFn (Cast Bits64Type Bits16Type) [a] = pure $ MkPrimFnRes [SBits64] SBits16 $ \[a] => fnCall "Int64.to_int32" [a]
-- to Bits32
mlPrimFn (Cast IntType Bits32Type) [a] = pure $ MkPrimFnRes [SInt] SBits32 $ \[a] => fnCall "Int32.of_int" [a]
mlPrimFn (Cast IntegerType Bits32Type) [a] = pure $ MkPrimFnRes [SInteger] SBits32 $ \[a] => fnCall "Int64.to_int32" [a]
mlPrimFn (Cast Bits8Type Bits32Type) [a] = pure $ MkPrimFnRes [SBits8] SBits32 $ \[a] => a
mlPrimFn (Cast Bits16Type Bits32Type) [a] = pure $ MkPrimFnRes [SBits16] SBits32 $ \[a] => a
mlPrimFn (Cast Bits64Type Bits32Type) [a] = pure $ MkPrimFnRes [SBits64] SBits32 $ \[a] => fnCall "Int64.to_int32" [a]
-- to Bits64
mlPrimFn (Cast IntType Bits64Type) [a] = pure $ MkPrimFnRes [SInt] SBits64 $ \[a] => fnCall "Int64.of_int" [a]
mlPrimFn (Cast IntegerType Bits64Type) [a] = pure $ MkPrimFnRes [SInteger] SBits64 $ \[a] => a -- TODO handle overflow
mlPrimFn (Cast Bits8Type Bits64Type) [a] = pure $ MkPrimFnRes [SBits8] SBits64 $ \[a] => fnCall "Int64.of_int32" [a]
mlPrimFn (Cast Bits16Type Bits64Type) [a] = pure $ MkPrimFnRes [SBits16] SBits64 $ \[a] => fnCall "Int64.of_int32" [a]
mlPrimFn (Cast Bits32Type Bits64Type) [a] = pure $ MkPrimFnRes [SBits32] SBits64 $ \[a] => fnCall "Int64.of_int32" [a]

{-

schOp (Cast IntType StringType) [x] = op "number->string" [x]
schOp (Cast IntegerType StringType) [x] = op "number->string" [x]
schOp (Cast Bits8Type StringType) [x] = op "number->string" [x]
schOp (Cast Bits16Type StringType) [x] = op "number->string" [x]
schOp (Cast Bits32Type StringType) [x] = op "number->string" [x]
schOp (Cast Bits64Type StringType) [x] = op "number->string" [x]
schOp (Cast DoubleType StringType) [x] = op "number->string" [x]
schOp (Cast CharType StringType) [x] = op "string" [x]

schOp (Cast IntegerType DoubleType) [x] = op "exact->inexact" [x]
schOp (Cast IntType DoubleType) [x] = op "exact->inexact" [x]
schOp (Cast StringType DoubleType) [x] = op "cast-string-double" [x]

schOp (Cast IntType CharType) [x] = op "cast-int-char" [x]

schOp (Cast from to) [x] = "(blodwen-error-quit \"Invalid cast " ++ show from ++ "->" ++ show to ++ "\")"
-}

mlPrimFn fn args = throw . InternalError $ "Unsupported primitive function " ++ show fn ++ " with args: " ++ show args


mutual
    castedExpr : {auto di : DefInfos} ->
                 {auto funArgs : NameMap SType } ->
                 SType ->
                 NamedCExp ->
                 Core MLExpr
    castedExpr SErased _ = pure $ MkMLExpr "()" SErased
    castedExpr ty expr = do
        expr' <- mlExpr expr
        case maybeCastFn expr'.type ty of
            Nothing => pure expr'
            Just fn => pure $ MkMLExpr (fnCall fn [expr'.source]) ty

    export
    mlExpr : {auto di : DefInfos} ->
            {auto funArgs : NameMap SType } ->
            NamedCExp -> Core MLExpr
    mlExpr (NmLocal fc x) = do
        let ty = fromMaybe SOpaque (lookup x funArgs)
        let source = mlName x
        pure $ MkMLExpr source ty
    mlExpr (NmRef fc x) =
        let source = fnCall "as_opaque" [mlName x]
            type = SOpaque
        in pure $ MkMLExpr source type
    mlExpr (NmLam fc x expr) = do
        expr' <- mlExpr expr
        let source = "(as_opaque (fun (" ++ mlName x ++ " : idr2_opaque) : idr2_opaque -> Obj.magic ("
                ++ expr'.source
                ++ ")))"
            type = SOpaque
        pure $ MkMLExpr source type
    mlExpr (NmLet fc x rhs expr) = do
        rhs' <- mlExpr rhs
        let funArgs' = insert x rhs'.type funArgs
        expr' <- mlExpr {funArgs = funArgs'} expr
        let source = "(let " ++ mlName x ++ " = " ++ rhs'.source ++ " in " ++ expr'.source ++ ")"
        let type = expr'.type
        pure $ MkMLExpr source type
    mlExpr (NmApp fc (NmRef _ name) args) = do
        args' <- traverse mlExpr args
        case lookup name di of
            Just tyInfo => do
                args <- traverse (uncurry castedExpr) (tyInfo.argTypes `zip` args)
                let call = fnCall (mlName name) (map source args)
                pure $ MkMLExpr call tyInfo.restType
                
            Nothing => throw $ InternalError ("Unsupported function " ++ show name)

    mlExpr (NmApp fc base args) = do
        base' <- mlExpr base
        args' <- traverse mlExpr args

        let src = fnCall "hint_opaque" [fnCall "as_fun" (base'.source :: map source args')]
            type = SOpaque
        pure $ MkMLExpr src type

    mlExpr (NmCon fc name tag args) = do
        let tag' = fromMaybe 0 tag
        case lookup name di of
            Just tyInfo => do
                args' <- traverse (uncurry castedExpr) (tyInfo.argTypes `zip` args)
                let argsArray = "(" ++ showSep ", " (map source args') ++ ")"
                    src = "(as_opaque (" ++ show tag' ++ ", as_opaque " ++ argsArray ++ "))"
                pure $ MkMLExpr src SOpaque
            Nothing => do
                args' <- traverse (castedExpr SOpaque) args
                let argsArray = "(" ++ showSep ", " (map source args') ++ ")"
                    src = "(as_opaque (" ++ show tag' ++ ", as_opaque " ++ argsArray ++ "))"
                pure $ MkMLExpr src SOpaque

    mlExpr (NmOp fc fn args) = do
        res <- mlPrimFn fn args
        args' <- traverse (uncurry castedExpr) $ res.argTypes `zip` args
        let src = res.printer (map source args')
        pure $ MkMLExpr src res.retType

    mlExpr (NmExtPrim fc p xs) = pure empty --?mlExpr_rhs_8
    mlExpr (NmForce fc x) = pure empty --?mlExpr_rhs_9
    mlExpr (NmDelay fc x) = pure empty --?mlExpr_rhs_10
    mlExpr (NmConCase fc sc xs x) = pure empty --?mlExpr_rhs_11
    mlExpr (NmConstCase fc sc xs x) = pure empty --?mlExpr_rhs_12
    mlExpr (NmPrimVal fc val) = mlPrimVal val
    mlExpr (NmErased fc) = pure $ MkMLExpr "()" SErased
    mlExpr (NmCrash fc x) = 
        let source = fnCall "raise" [fnCall "Idris2_Exception" [show x]]
            type = SOpaque
        in pure $ MkMLExpr source type

