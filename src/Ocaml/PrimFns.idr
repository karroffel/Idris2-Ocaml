||| Code generation for primitive functions
module Ocaml.PrimFns

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.Vect

import Ocaml.DefInfo
import Ocaml.Utils

||| Delayed code generation of a primitive function.
|||
||| Because the code for compiling expressions is in an unaccessible module
||| the expected types are reported and a printing function `printer` is
||| provided which works on `String`s instead.
public export
record PrimFnRes (arity : Nat) where
    constructor MkPrimFnRes
    argTypes : Vect arity SType
    retType : SType
    printer : Vect arity String -> String

binaryPrimFn : {arity : Nat} -> SType -> (Vect arity String -> String) -> Core (PrimFnRes arity)
binaryPrimFn ty fn = pure $ MkPrimFnRes (replicate arity ty) ty fn


bits8Bound : String -> String
bits8Bound s = fnCall "ensure_bits8" [s]

bits16Bound : String -> String
bits16Bound s = fnCall "ensure_bits16" [s]

bits32Bound : String -> String
bits32Bound s = fnCall "ensure_bits32" [s]


addFn : Constant -> Core (PrimFnRes 2)
addFn ty = do
    fn <- case ty of
        IntType => pure $ \[a, b] => binOp "+" a b
        IntegerType => pure $ \[a, b] => fnCall "Z.add" [a, b]
        Bits8Type => pure $ \[a, b] => bits8Bound $ binOp "+" a b
        Bits16Type => pure $ \[a, b] => bits16Bound $ binOp "+" a b
        Bits32Type => pure $ \[a, b] => bits32Bound $ binOp "+" a b
        Bits64Type => pure $ \[a, b] => fnCall "Int64.add" [a, b]
        DoubleType => pure $ \[a, b] => binOp "+." a b
        _ => throw . InternalError $ "Unsupported add implementation for type " ++ show ty
    binaryPrimFn (stypeFromConst ty) fn

subFn : Constant -> Core (PrimFnRes 2)
subFn ty = do
    fn <- case ty of
        IntType => pure $ \[a, b] => binOp "-" a b
        IntegerType => pure $ \[a, b] => fnCall "Z.sub" [a, b]
        Bits8Type => pure $ \[a, b] => bits8Bound $ binOp "-" a b
        Bits16Type => pure $ \[a, b] => bits16Bound $ binOp "-" a b
        Bits32Type => pure $ \[a, b] => bits32Bound $ binOp "-" a b
        Bits64Type => pure $ \[a, b] => fnCall "Int64.sub" [a, b]
        DoubleType => pure $ \[a, b] => binOp "-." a b
        _ => throw . InternalError $ "Unsupported sub implementation for type " ++ show ty
    binaryPrimFn (stypeFromConst ty) fn

mulFn : Constant -> Core (PrimFnRes 2)
mulFn ty = do
    fn <- case ty of
        IntType => pure $ \[a, b] => binOp "*" a b
        IntegerType => pure $ \[a, b] => fnCall "Z.mul" [a, b]
        Bits8Type => pure $ \[a, b] => bits8Bound $ binOp "*" a b
        Bits16Type => pure $ \[a, b] => bits16Bound $ binOp "*" a b
        Bits32Type => pure $ \[a, b] => bits32Bound $ binOp "*" a b
        Bits64Type => pure $ \[a, b] => fnCall "Int64.mul" [a, b]
        DoubleType => pure $ \[a, b] => binOp "*." a b
        _ => throw . InternalError $ "Unsupported mul implementation for type " ++ show ty
    binaryPrimFn (stypeFromConst ty) fn

divFn : Constant -> Core (PrimFnRes 2)
divFn ty = do
    fn <- case ty of
        IntType => pure $ \[a, b] => binOp "/" a b
        IntegerType => pure $ \[a, b] => fnCall "Z.div" [a, b]
        Bits8Type => pure $ \[a, b] => bits8Bound $ binOp "/" a b
        Bits16Type => pure $ \[a, b] => bits16Bound $ binOp "/" a b
        Bits32Type => pure $ \[a, b] => bits32Bound $ binOp "/" a b
        Bits64Type => pure $ \[a, b] => fnCall "Int64.unsigned_div" [a, b]
        DoubleType => pure $ \[a, b] => binOp "/." a b
        _ => throw . InternalError $ "Unsupported div implementation for type " ++ show ty
    binaryPrimFn (stypeFromConst ty) fn

modFn : Constant -> Core (PrimFnRes 2)
modFn ty = do
    fn <- case ty of
        IntType => pure $ \[a, b] => binOp "mod" a b
        IntegerType => pure $ \[a, b] => fnCall "Z.rem" [a, b]
        Bits8Type => pure $ \[a, b] => bits8Bound $ binOp "mod" a b
        Bits16Type => pure $ \[a, b] => bits16Bound $ binOp "mod" a b
        Bits32Type => pure $ \[a, b] => bits32Bound $ binOp "mod" a b
        Bits64Type => pure $ \[a, b] => fnCall "Int64.unsigned_rem" [a, b]
        _ => throw . InternalError $ "Unsupported mod implementation for type " ++ show ty
    binaryPrimFn (stypeFromConst ty) fn

shiftLFn : Constant -> Core (PrimFnRes 2)
shiftLFn ty = do
    fn <- case ty of
        IntType => pure $ \[a, b] => binOp "lsl" a b
        IntegerType => pure $ \[a, b] => fnCall "Z.shift_left" [a, fnCall "Z.to_int" [b]]
        Bits8Type => pure $ \[a, b] => bits8Bound $ binOp "lsl" a b
        Bits16Type => pure $ \[a, b] => bits16Bound $ binOp "lsl" a b
        Bits32Type => pure $ \[a, b] => bits32Bound $ binOp "lsl" a b
        Bits64Type => pure $ \[a, b] => fnCall "Int64.shift_left" [a, fnCall "Int64.to_int" [b]]
        _ => throw . InternalError $ "Unsupported shiftL implementation for type " ++ show ty
    binaryPrimFn (stypeFromConst ty) fn

shiftRFn : Constant -> Core (PrimFnRes 2)
shiftRFn ty = do
    fn <- case ty of
        IntType => pure $ \[a, b] => binOp "lsr" a b
        IntegerType => pure $ \[a, b] => fnCall "Z.shift_right" [a, fnCall "Z.to_int" [b]]
        Bits8Type => pure $ \[a, b] => bits8Bound $ binOp "lsr" a b
        Bits16Type => pure $ \[a, b] => bits16Bound $ binOp "lsr" a b
        Bits32Type => pure $ \[a, b] => bits32Bound $ binOp "lsr" a b
        Bits64Type => pure $ \[a, b] => fnCall "Int64.shift_right" [a, fnCall "Int64.to_int" [b]]
        _ => throw . InternalError $ "Unsupported shiftR implementation for type " ++ show ty
    binaryPrimFn (stypeFromConst ty) fn

castToInt : Constant -> Core (PrimFnRes 1)
castToInt ty = do
    fn <- case ty of
        IntegerType => pure $ \[a] => fnCall "cast_bint_int" [a]
        Bits8Type => pure $ \[a] => a
        Bits16Type => pure $ \[a] => a
        Bits32Type => pure $ \[a] => a
        Bits64Type => pure $ \[a] => fnCall "cast_bit64_int" [a]
        DoubleType => pure $ \[a] => fnCall "int_of_float" [a]
        StringType => pure $ \[a] => fnCall "int_of_string" [a]
        CharType => pure $ \[a] => fnCall "int_of_char" [a]
        _ => throw . InternalError $ "Unsupported cast to Int implementation for type " ++ show ty
    pure $ MkPrimFnRes [stypeFromConst ty] SInt fn

castToInteger : Constant -> Core (PrimFnRes 1)
castToInteger ty = do
    fn <- case ty of
        IntType => pure $ \[a] => fnCall "Z.of_int" [a]
        Bits8Type => pure $ \[a] => fnCall "Z.of_int" [a]
        Bits16Type => pure $ \[a] => fnCall "Z.of_int" [a]
        Bits32Type => pure $ \[a] => fnCall "Z.of_int" [a]
        Bits64Type => pure $ \[a] => fnCall "Z.of_int64" [a]
        DoubleType => pure $ \[a] => fnCall "Z.of_float" [a]
        CharType => pure $ \[a] => fnCall "Z.of_int" [fnCall "int_of_char" [a]]
        StringType => pure $ \[a] => fnCall "Z.of_string" [a]
        _ => throw . InternalError $ "Unsupported cast to Integer implementation for type " ++ show ty
    pure $ MkPrimFnRes [stypeFromConst ty] SInteger fn


castToBits8 : Constant -> Core (PrimFnRes 1)
castToBits8 ty = do
    fn <- case ty of
        IntType => pure $ \[a] => fnCall "cast_int_bits8" [a]
        IntegerType => pure $ \[a] => fnCall "cast_bint_bits8" [a]
        Bits16Type => pure $ \[a] => fnCall "cast_int_bits8" [a]
        Bits32Type => pure $ \[a] => fnCall "cast_int_bits8" [a]
        Bits64Type => pure $ \[a] => fnCall "cast_bits64_bits8" [a]
        _ => throw . InternalError $ "Unsupported cast to Bits8 implementation for type " ++ show ty
    pure $ MkPrimFnRes [stypeFromConst ty] SBits8 fn

castToBits16 : Constant -> Core (PrimFnRes 1)
castToBits16 ty = do
    fn <- case ty of
        IntType => pure $ \[a] => fnCall "cast_int_bits16" [a]
        IntegerType => pure $ \[a] => fnCall "cast_bint_bits16" [a]
        Bits8Type => pure $ \[a] => a
        Bits32Type => pure $ \[a] => fnCall "cast_int_bits16" [a]
        Bits64Type => pure $ \[a] => fnCall "cast_bits64_bits8" [a]
        _ => throw . InternalError $ "Unsupported cast to Bits16 implementation for type " ++ show ty
    pure $ MkPrimFnRes [stypeFromConst ty] SBits16 fn

castToBits32 : Constant -> Core (PrimFnRes 1)
castToBits32 ty = do
    fn <- case ty of
        IntType => pure $ \[a] => fnCall "cast_int_bits32" [a]
        IntegerType => pure $ \[a] => fnCall "cast_bint_bits32" [a]
        Bits8Type => pure $ \[a] => a
        Bits16Type => pure $ \[a] => a
        Bits64Type => pure $ \[a] => fnCall "cast_bits64_bits32" [a]
        _ => throw . InternalError $ "Unsupported cast to Bits32 implementation for type " ++ show ty
    pure $ MkPrimFnRes [stypeFromConst ty] SBits32 fn

castToBits64 : Constant -> Core (PrimFnRes 1)
castToBits64 ty = do
    fn <- case ty of
        IntType => pure $ \[a] => fnCall "Int64.of_int" [a]
        IntegerType => pure $ \[a] => fnCall "cast_bint_bits64" [a]
        Bits8Type => pure $ \[a] => fnCall "Int64.of_int" [a]
        Bits16Type => pure $ \[a] => fnCall "Int64.of_int" [a]
        Bits32Type => pure $ \[a] => fnCall "Int64.of_int" [a]
        _ => throw . InternalError $ "Unsupported cast to Bits64 implementation for type " ++ show ty
    pure $ MkPrimFnRes [stypeFromConst ty] SBits64 fn

castToString : Constant -> Core (PrimFnRes 1)
castToString ty = do
    fn <- case ty of
        IntType => pure $ \[a] => fnCall "string_of_int" [a]
        IntegerType => pure $ \[a] => fnCall "Z.to_string" [a]
        Bits8Type => pure $ \[a] => fnCall "string_of_int" [a]
        Bits16Type => pure $ \[a] => fnCall "string_of_int" [a]
        Bits32Type => pure $ \[a] => fnCall "string_of_int" [a]
        Bits64Type => pure $ \[a] => fnCall "Int64.to_string" [a] -- TODO this behaves like signed ints
        DoubleType => pure $ \[a] => fnCall "string_of_float" [a]
        CharType => pure $ \[a] => fnCall "OcamlRts.String.of_char" [a]
        _ => throw . InternalError $ "Unsupported cast to String implementation for type " ++ show ty
    pure $ MkPrimFnRes [stypeFromConst ty] SString fn

castToDouble : Constant -> Core (PrimFnRes 1)
castToDouble ty = do
    fn <- case ty of
        IntType => pure $ \[a] => fnCall "float_of_int" [a]
        IntegerType => pure $ \[a] => fnCall "Z.to_float" [a]
        StringType => pure $ \[a] => fnCall "float_of_string" [a]
        _ => throw . InternalError $ "Unsupported cast to Double implementation for type " ++ show ty
    pure $ MkPrimFnRes [stypeFromConst ty] SDouble fn


doubleFn : String -> PrimFnRes 1
doubleFn name = MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall name [a]


export
mlPrimFn : PrimFn arity -> Vect arity NamedCExp -> Core (PrimFnRes arity)
mlPrimFn (Add ty) _ = addFn ty
mlPrimFn (Sub ty) _ = subFn ty
mlPrimFn (Mul ty) _ = mulFn ty
mlPrimFn (Div ty) _ = divFn ty
mlPrimFn (Mod ty) _ = modFn ty
mlPrimFn (Neg IntType) [a] = pure $ MkPrimFnRes [SInt] SInt $ \[a] => fnCall "-" [a]
mlPrimFn (Neg IntegerType) [a] = pure $ MkPrimFnRes [SInteger] SInteger $ \[a] => fnCall "Z.neg" [a]
mlPrimFn (Neg DoubleType) [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "-." [a]
mlPrimFn (ShiftL ty) _ = shiftLFn ty
mlPrimFn (ShiftR ty) _ = shiftLFn ty
mlPrimFn (BAnd IntType) _ = binaryPrimFn SInt $ \[a, b] => fnCall "Int.logand" [a, b]
mlPrimFn (BAnd IntegerType) _ = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.logand" [a, b]
mlPrimFn (BAnd Bits8Type) _ = binaryPrimFn SBits8 $ \[a, b] => bits8Bound (fnCall "Int.logand" [a, b])
mlPrimFn (BAnd Bits16Type) _ = binaryPrimFn SBits16 $ \[a, b] => bits16Bound (fnCall "Int.logand" [a, b])
mlPrimFn (BAnd Bits32Type) _ = binaryPrimFn SBits32 $ \[a, b] => bits32Bound (fnCall "Int.logand" [a, b])
mlPrimFn (BAnd Bits64Type) _ = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.logand" [a, b]
mlPrimFn (BAnd ty) args = throw $ InternalError ("unimplemented bitwise-and for type " ++ show ty)
mlPrimFn (BOr IntType) _ = binaryPrimFn SInt $ \[a, b] => fnCall "Int.logor" [a, b]
mlPrimFn (BOr IntegerType) _ = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.logor" [a, b]
mlPrimFn (BOr Bits8Type) _ = binaryPrimFn SBits8 $ \[a, b] => bits8Bound (fnCall "Int.logor" [a, b])
mlPrimFn (BOr Bits16Type) _ = binaryPrimFn SBits16 $ \[a, b] => bits16Bound (fnCall "Int.logor" [a, b])
mlPrimFn (BOr Bits32Type) _ = binaryPrimFn SBits32 $ \[a, b] => bits32Bound (fnCall "Int.logor" [a, b])
mlPrimFn (BOr Bits64Type) _ = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.logor" [a, b]
mlPrimFn (BOr ty) args = throw $ InternalError ("unimplemented bitwise-or for type " ++ show ty)
mlPrimFn (BXOr IntType) _ = binaryPrimFn SInt $ \[a, b] => fnCall "Int.logxor" [a, b]
mlPrimFn (BXOr IntegerType) _ = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.logxor" [a, b]
mlPrimFn (BXOr Bits8Type) _ = binaryPrimFn SBits8 $ \[a, b] => bits8Bound (fnCall "Int.logxor" [a, b])
mlPrimFn (BXOr Bits16Type) _ = binaryPrimFn SBits16 $ \[a, b] => bits16Bound (fnCall "Int.logxor" [a, b])
mlPrimFn (BXOr Bits32Type) _ = binaryPrimFn SBits32 $ \[a, b] => bits32Bound (fnCall "Int.logxor" [a, b])
mlPrimFn (BXOr Bits64Type) _ = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.logxor" [a, b]
mlPrimFn (BXOr ty) args = throw $ InternalError ("unimplemented bitwise-xor for type " ++ show ty)
mlPrimFn (LT ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp "<" a b
mlPrimFn (LTE ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp "<=" a b
mlPrimFn (EQ ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp "==" a b
mlPrimFn (GTE ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp ">=" a b
mlPrimFn (GT ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp ">" a b
mlPrimFn StrLength [a] = pure $ MkPrimFnRes [SString] SInt $ \[a] => fnCall "OcamlRts.String.length" [a]
mlPrimFn StrHead [a] = pure $ MkPrimFnRes [SString] SChar $ \[a] => fnCall "OcamlRts.String.head" [a]
mlPrimFn StrTail [a] = pure $ MkPrimFnRes [SString] SString $ \[a] => fnCall "OcamlRts.String.tail" [a]
mlPrimFn StrIndex [s, i] = pure $ MkPrimFnRes [SString, SInt] SChar $ \[a, i] => fnCall "OcamlRts.String.get" [a, i]
mlPrimFn StrCons [c, s] = pure $ MkPrimFnRes [SChar, SString] SString $ \[c, s] => fnCall "OcamlRts.String.cons" [c, s]
mlPrimFn StrAppend [a, b] = pure $ MkPrimFnRes [SString, SString] SString $ \[a, b] => binOp "^" a b
mlPrimFn StrReverse [a] = pure $ MkPrimFnRes [SString] SString $ \[a] => fnCall "OcamlRts.String.reverse" [a]
mlPrimFn StrSubstr [offset, len, s] = pure $ MkPrimFnRes [SInt, SInt, SString] SString $ \[offset, len, s] => fnCall "OcamlRts.String.substring" [offset, len, s]
mlPrimFn DoubleExp _ = pure $ doubleFn "Float.exp"
mlPrimFn DoubleLog _ = pure $ doubleFn "Float.log"
mlPrimFn DoubleSin _ = pure $ doubleFn "Float.sin"
mlPrimFn DoubleCos _ = pure $ doubleFn "Float.cos"
mlPrimFn DoubleTan _ = pure $ doubleFn "Float.tan"
mlPrimFn DoubleASin _ = pure $ doubleFn "Float.asin"
mlPrimFn DoubleACos _ = pure $ doubleFn "Float.acos"
mlPrimFn DoubleATan _ = pure $ doubleFn "Float.atan"
mlPrimFn DoubleSqrt _ = pure $ doubleFn "Float.sqrt"
mlPrimFn DoubleFloor _ = pure $ doubleFn "Float.floor"
mlPrimFn DoubleCeiling _ = pure $ doubleFn "Float.ceil"
mlPrimFn BelieveMe [_, _, x] = pure $ MkPrimFnRes [SErased, SErased, SOpaque] SOpaque $ \[_, _, x] => x
mlPrimFn Crash [_, msg] = pure $ MkPrimFnRes [SErased, SString] SOpaque $ \[_, msg] => fnCall "raise" [fnCall "Idris2_Exception" [msg]]
mlPrimFn (Cast ty IntType) _ = castToInt ty
mlPrimFn (Cast ty IntegerType) _ = castToInteger ty
mlPrimFn (Cast ty Bits8Type) _ = castToBits8 ty
mlPrimFn (Cast ty Bits16Type) _ = castToBits16 ty
mlPrimFn (Cast ty Bits32Type) _ = castToBits32 ty
mlPrimFn (Cast ty Bits64Type) _ = castToBits64 ty
mlPrimFn (Cast ty StringType) _ = castToString ty
mlPrimFn (Cast ty DoubleType) _ = castToDouble ty
mlPrimFn (Cast IntType CharType) [a] = pure $ MkPrimFnRes [SInt] SChar $ \[a] => fnCall "char_of_int" [a]
mlPrimFn (Cast from to) _ = throw . InternalError $ "Invalid cast " ++ show from ++ " -> " ++ show to
mlPrimFn fn args = throw . InternalError $ "Unsupported primitive function " ++ show fn ++ " with args: " ++ show args

