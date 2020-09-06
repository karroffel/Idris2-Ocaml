||| Code generation for primitive functions
module Ocaml.PrimFns

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.Vect

import Ocaml.DefInfo
import Ocaml.Utils

bits8Bound : String -> String
bits8Bound s = fnCall "ensure_bits8" [s]

bits16Bound : String -> String
bits16Bound s = fnCall "ensure_bits16" [s]

bits32Bound : String -> String
bits32Bound s = fnCall "ensure_bits32" [s]


castFnForTy : Constant -> Core (String -> String)
castFnForTy IntType = pure asInt
castFnForTy IntegerType = pure asBint
castFnForTy Bits8Type = pure asBits8
castFnForTy Bits16Type = pure asBits16
castFnForTy Bits32Type = pure asBits32
castFnForTy Bits64Type = pure asBits64
castFnForTy StringType = pure asString
castFnForTy CharType = pure asChar
castFnForTy DoubleType = pure asDouble
castFnForTy ty = throw . InternalError $ "Unsupported type " ++ show ty

binFn : (castFn : String -> String) -> (Vect 2 String -> String) -> Vect 2 String -> Core String
binFn castFn f args = pure . mlRepr . f $ map castFn args


addFn : Constant -> Vect 2 String -> Core String
addFn ty args = do
    fn <- case ty of
        IntType => pure $ binFn asInt \[a, b] => binOp "+" a b
        IntegerType => pure $ binFn asBint \[a, b] => fnCall "Z.add" [a, b]
        Bits8Type => pure $ binFn asBits8 \[a, b] => bits8Bound $ binOp "+" a b
        Bits16Type => pure $ binFn asBits16 \[a, b] => bits16Bound $ binOp "+" a b
        Bits32Type => pure $ binFn asBits32 \[a, b] => bits32Bound $ binOp "+" a b
        Bits64Type => pure $ binFn asBits64 \[a, b] => fnCall "Int64.add" [a, b]
        DoubleType => pure $ binFn asDouble \[a, b] => binOp "+." a b
        _ => throw . InternalError $ "Unsupported add implementation for type " ++ show ty
    fn args

subFn : Constant -> Vect 2 String -> Core String
subFn ty args = do
    fn <- case ty of
        IntType => pure $ binFn asInt \[a, b] => binOp "-" a b
        IntegerType => pure $ binFn asBint \[a, b] => fnCall "Z.sub" [a, b]
        Bits8Type => pure $ binFn asBits8 \[a, b] => bits8Bound $ binOp "-" a b
        Bits16Type => pure $ binFn asBits16 \[a, b] => bits16Bound $ binOp "-" a b
        Bits32Type => pure $ binFn asBits32 \[a, b] => bits32Bound $ binOp "-" a b
        Bits64Type => pure $ binFn asBits64 \[a, b] => fnCall "Int64.sub" [a, b]
        DoubleType => pure $ binFn asDouble \[a, b] => binOp "-." a b
        _ => throw . InternalError $ "Unsupported sub implementation for type " ++ show ty
    fn args

mulFn : Constant -> Vect 2 String -> Core String
mulFn ty args = do
    fn <- case ty of
        IntType => pure $ binFn asInt \[a, b] => binOp "*" a b
        IntegerType => pure $ binFn asBint \[a, b] => fnCall "Z.mul" [a, b]
        Bits8Type => pure $ binFn asBits8 \[a, b] => bits8Bound $ binOp "*" a b
        Bits16Type => pure $ binFn asBits16 \[a, b] => bits16Bound $ binOp "*" a b
        Bits32Type => pure $ binFn asBits32 \[a, b] => bits32Bound $ binOp "*" a b
        Bits64Type => pure $ binFn asBits64 \[a, b] => fnCall "Int64.mul" [a, b]
        DoubleType => pure $ binFn asDouble \[a, b] => binOp "*." a b
        _ => throw . InternalError $ "Unsupported mul implementation for type " ++ show ty
    fn args

divFn : Constant -> Vect 2 String -> Core String
divFn ty args = do
    fn <- case ty of
        IntType => pure $ binFn asInt \[a, b] => binOp "/" a b
        IntegerType => pure $ binFn asBint \[a, b] => fnCall "Z.div" [a, b]
        Bits8Type => pure $ binFn asBits8 \[a, b] => bits8Bound $ binOp "/" a b
        Bits16Type => pure $ binFn asBits16 \[a, b] => bits16Bound $ binOp "/" a b
        Bits32Type => pure $ binFn asBits32 \[a, b] => bits32Bound $ binOp "/" a b
        Bits64Type => pure $ binFn asBits64 \[a, b] => fnCall "Int64.unsigned_div" [a, b]
        DoubleType => pure $ binFn asDouble \[a, b] => binOp "/." a b
        _ => throw . InternalError $ "Unsupported div implementation for type " ++ show ty
    fn args

modFn : Constant -> Vect 2 String -> Core String
modFn ty args = do
    fn <- case ty of
        IntType => pure $ binFn asInt \[a, b] => binOp "mod" a b
        IntegerType => pure $ binFn asBint \[a, b] => fnCall "Z.rem" [a, b]
        Bits8Type => pure $ binFn asBits8 \[a, b] => bits8Bound $ binOp "mod" a b
        Bits16Type => pure $ binFn asBits16 \[a, b] => bits16Bound $ binOp "mod" a b
        Bits32Type => pure $ binFn asBits32 \[a, b] => bits32Bound $ binOp "mod" a b
        Bits64Type => pure $ binFn asBits64 \[a, b] => fnCall "Int64.unsigned_rem" [a, b]
        _ => throw . InternalError $ "Unsupported mod implementation for type " ++ show ty
    fn args

shiftLFn : Constant -> Vect 2 String -> Core String
shiftLFn ty args = do
    fn <- case ty of
        IntType => pure $ binFn asInt \[a, b] => binOp "lsl" a b
        IntegerType => pure $ binFn asBint \[a, b] => fnCall "Z.shift_left" [a, fnCall "Z.to_int" [b]]
        Bits8Type => pure $ binFn asBits8 \[a, b] => bits8Bound $ binOp "lsl" a b
        Bits16Type => pure $ binFn asBits16 \[a, b] => bits16Bound $ binOp "lsl" a b
        Bits32Type => pure $ binFn asBits32 \[a, b] => bits32Bound $ binOp "lsl" a b
        Bits64Type => pure $ binFn asBits64 \[a, b] => fnCall "Int64.shift_left" [a, fnCall "Int64.to_int" [b]]
        _ => throw . InternalError $ "Unsupported shiftL implementation for type " ++ show ty
    fn args

shiftRFn : Constant -> Vect 2 String -> Core String
shiftRFn ty args = do
    fn <- case ty of
        IntType => pure $ binFn asInt \[a, b] => binOp "lsr" a b
        IntegerType => pure $ binFn asBint \[a, b] => fnCall "Z.shift_right" [a, fnCall "Z.to_int" [b]]
        Bits8Type => pure $ binFn asBits8 \[a, b] => bits8Bound $ binOp "lsr" a b
        Bits16Type => pure $ binFn asBits16 \[a, b] => bits16Bound $ binOp "lsr" a b
        Bits32Type => pure $ binFn asBits32 \[a, b] => bits32Bound $ binOp "lsr" a b
        Bits64Type => pure $ binFn asBits64 \[a, b] => fnCall "Int64.shift_right" [a, fnCall "Int64.to_int" [b]]
        _ => throw . InternalError $ "Unsupported shiftR implementation for type " ++ show ty
    fn args

castToInt : Constant -> String -> Core String
castToInt ty a = do
    case ty of
        IntegerType => pure . mlRepr $ fnCall "cast_bint_int" [asBint a]
        Bits8Type => pure a
        Bits16Type => pure a
        Bits32Type => pure a
        Bits64Type => pure . mlRepr $ fnCall "cast_bit64_int" [asBits64 a]
        DoubleType => pure . mlRepr $ fnCall "int_of_float" [asDouble a]
        StringType => pure . mlRepr $ fnCall "int_of_string" [asString a]
        CharType => pure . mlRepr $  fnCall "int_of_char" [asChar a]
        _ => throw . InternalError $ "Unsupported cast to Int implementation for type " ++ show ty

castToInteger : Constant -> String -> Core String
castToInteger ty a = do
    case ty of
        IntType => pure . mlRepr $ fnCall "Z.of_int" [asInt a]
        Bits8Type => pure . mlRepr $ fnCall "Z.of_int" [asBits8 a]
        Bits16Type => pure . mlRepr $ fnCall "Z.of_int" [asBits16 a]
        Bits32Type => pure . mlRepr $ fnCall "Z.of_int" [asBits32 a]
        Bits64Type => pure . mlRepr $ fnCall "Z.of_int64" [asBits64 a]
        DoubleType => pure . mlRepr $ fnCall "Z.of_float" [asDouble a]
        CharType => pure . mlRepr $ fnCall "Z.of_int" [fnCall "int_of_char" [asChar a]]
        StringType => pure . mlRepr $ fnCall "Z.of_string" [asString a]
        _ => throw . InternalError $ "Unsupported cast to Integer implementation for type " ++ show ty


castToBits8 : Constant -> String -> Core String
castToBits8 ty a = do
    case ty of
        IntType => pure . mlRepr $ fnCall "cast_int_bits8" [asInt a]
        IntegerType => pure . mlRepr $ fnCall "cast_bint_bits8" [asBint a]
        Bits16Type => pure . mlRepr $ fnCall "cast_int_bits8" [asBits16 a]
        Bits32Type => pure . mlRepr $ fnCall "cast_int_bits8" [asBits32 a]
        Bits64Type => pure . mlRepr $ fnCall "cast_bits64_bits8" [asBits64 a]
        _ => throw . InternalError $ "Unsupported cast to Bits8 implementation for type " ++ show ty

castToBits16 : Constant -> String -> Core String
castToBits16 ty a = do
    case ty of
        IntType => pure . mlRepr $ fnCall "cast_int_bits16" [asInt a]
        IntegerType => pure . mlRepr $ fnCall "cast_bint_bits16" [asBint a]
        Bits8Type => pure a
        Bits32Type => pure . mlRepr $ fnCall "cast_int_bits16" [asBits32 a]
        Bits64Type => pure . mlRepr $ fnCall "cast_bits64_bits8" [asBits64 a]
        _ => throw . InternalError $ "Unsupported cast to Bits16 implementation for type " ++ show ty

castToBits32 : Constant -> String -> Core String
castToBits32 ty a = do
    case ty of
        IntType => pure . mlRepr $ fnCall "cast_int_bits32" [asInt a]
        IntegerType => pure . mlRepr $ fnCall "cast_bint_bits32" [asBint a]
        Bits8Type => pure a
        Bits16Type => pure a
        Bits64Type => pure . mlRepr $ fnCall "cast_bits64_bits32" [asBits64 a]
        _ => throw . InternalError $ "Unsupported cast to Bits32 implementation for type " ++ show ty

castToBits64 : Constant -> String -> Core String
castToBits64 ty a = do
    case ty of
        IntType => pure . mlRepr $ fnCall "Int64.of_int" [asInt a]
        IntegerType => pure . mlRepr $ fnCall "cast_bint_bits64" [asBint a]
        Bits8Type => pure . mlRepr $ fnCall "Int64.of_int" [asBits8 a]
        Bits16Type => pure . mlRepr $ fnCall "Int64.of_int" [asBits16 a]
        Bits32Type => pure . mlRepr $ fnCall "Int64.of_int" [asBits32 a]
        _ => throw . InternalError $ "Unsupported cast to Bits64 implementation for type " ++ show ty

castToString : Constant -> String -> Core String
castToString ty a = do
    case ty of
        IntType => pure . mlRepr $ fnCall "string_of_int" [asInt a]
        IntegerType => pure . mlRepr $ fnCall "Z.to_string" [asBint a]
        Bits8Type => pure . mlRepr $ fnCall "string_of_int" [asBits8 a]
        Bits16Type => pure . mlRepr $ fnCall "string_of_int" [asBits16 a]
        Bits32Type => pure . mlRepr $ fnCall "string_of_int" [asBits32 a]
        Bits64Type => pure . mlRepr $ fnCall "Int64.to_string" [asBits64 a] -- TODO this behaves like signed ints
        DoubleType => pure . mlRepr $ fnCall "string_of_float" [asDouble a]
        CharType => pure . mlRepr $ fnCall "OcamlRts.String.of_char" [asChar a]
        _ => throw . InternalError $ "Unsupported cast to String implementation for type " ++ show ty

castToDouble : Constant -> String -> Core String
castToDouble ty a = do
    case ty of
        IntType => pure . mlRepr $ fnCall "float_of_int" [asInt a]
        IntegerType => pure . mlRepr $ fnCall "Z.to_float" [asBint a]
        StringType => pure . mlRepr $ fnCall "float_of_string" [asString a]
        _ => throw . InternalError $ "Unsupported cast to Double implementation for type " ++ show ty


doubleFn : String -> Vect 1 String -> Core String
doubleFn name [a] = pure . mlRepr $ fnCall name [asDouble a]


export
mlPrimFn : PrimFn arity -> Vect arity String -> Core String
mlPrimFn (Add ty) args = addFn ty args
mlPrimFn (Sub ty) args = subFn ty args
mlPrimFn (Mul ty) args = mulFn ty args
mlPrimFn (Div ty) args = divFn ty args
mlPrimFn (Mod ty) args = modFn ty args
mlPrimFn (Neg IntType) [a] = pure . mlRepr $ fnCall "-" [asInt a]
mlPrimFn (Neg IntegerType) [a] = pure . mlRepr $ fnCall "Z.neg" [asBint a]
mlPrimFn (Neg DoubleType) [a] = pure . mlRepr $ fnCall "-." [asDouble a]
mlPrimFn (ShiftL ty) args = shiftLFn ty args
mlPrimFn (ShiftR ty) args = shiftRFn ty args
mlPrimFn (BAnd IntType) [a, b] = pure . mlRepr $ fnCall "Int.logand" [asInt a, asInt b]
mlPrimFn (BAnd IntegerType) [a, b] = pure . mlRepr $ fnCall "Z.logand" [asBint a, asBint b]
mlPrimFn (BAnd Bits8Type) [a, b] = pure . mlRepr . bits8Bound $ fnCall "Int.logand" [asBits8 a, asBits8 b]
mlPrimFn (BAnd Bits16Type) [a, b] = pure . mlRepr . bits16Bound $ fnCall "Int.logand" [asBits16 a, asBits16 b]
mlPrimFn (BAnd Bits32Type) [a, b] = pure . mlRepr . bits32Bound $ fnCall "Int.logand" [asBits32 a, asBits32 b]
mlPrimFn (BAnd Bits64Type) [a, b] = pure . mlRepr $ fnCall "Int64.logand" [asBits64 a, asBits64 b]
mlPrimFn (BAnd ty) args = throw $ InternalError ("unimplemented bitwise-and for type " ++ show ty)
mlPrimFn (BOr IntType) [a, b] = pure . mlRepr $ fnCall "Int.logor" [asInt a, asInt b]
mlPrimFn (BOr IntegerType) [a, b] = pure . mlRepr $ fnCall "Z.logor" [asBint a, asBint b]
mlPrimFn (BOr Bits8Type) [a, b] = pure . mlRepr . bits8Bound $ fnCall "Int.logor" [asBits8 a, asBits8 b]
mlPrimFn (BOr Bits16Type) [a, b] = pure . mlRepr . bits16Bound $ fnCall "Int.logor" [asBits16 a, asBits16 b]
mlPrimFn (BOr Bits32Type) [a, b] = pure . mlRepr . bits32Bound $ fnCall "Int.logor" [asBits32 a, asBits32 b]
mlPrimFn (BOr Bits64Type) [a, b] = pure . mlRepr $ fnCall "Int64.logor" [asBits64 a, asBits64 b]
mlPrimFn (BOr ty) args = throw $ InternalError ("unimplemented bitwise-or for type " ++ show ty)
mlPrimFn (BXOr IntType) [a, b] = pure . mlRepr $ fnCall "Int.logxor" [a, b]
mlPrimFn (BXOr IntegerType) [a, b] = pure . mlRepr $ fnCall "Z.logxor" [a, b]
mlPrimFn (BXOr Bits8Type) [a, b] = pure . mlRepr . bits8Bound $ fnCall "Int.logxor" [asBits8 a, asBits8 b]
mlPrimFn (BXOr Bits16Type) [a, b] = pure . mlRepr . bits16Bound $ fnCall "Int.logxor" [asBits16 a, asBits16 b]
mlPrimFn (BXOr Bits32Type) [a, b] = pure . mlRepr . bits32Bound $ fnCall "Int.logxor" [asBits32 a, asBits32 b]
mlPrimFn (BXOr Bits64Type) [a, b] = pure . mlRepr $ fnCall "Int64.logxor" [asBits64 a, asBits64 b]
mlPrimFn (BXOr ty) args = throw $ InternalError ("unimplemented bitwise-xor for type " ++ show ty)
mlPrimFn (LT ty) [a, b] = castFnForTy ty >>= \t => pure . mlRepr $ boolOp "<" (t a) (t b)
mlPrimFn (LTE ty) [a, b] = castFnForTy ty >>= \t => pure . mlRepr $ boolOp "<=" (t a) (t b)
mlPrimFn (EQ ty) [a, b] = castFnForTy ty >>= \t => pure . mlRepr $ boolOp "=" (t a) (t b)
mlPrimFn (GTE ty) [a, b] = castFnForTy ty >>= \t => pure . mlRepr $ boolOp ">=" (t a) (t b)
mlPrimFn (GT ty) [a, b] = castFnForTy ty >>= \t => pure . mlRepr $ boolOp ">" (t a) (t b)
mlPrimFn StrLength [a] = pure . mlRepr $ fnCall "OcamlRts.String.length" [asString a]
mlPrimFn StrHead [a] = pure . mlRepr $ fnCall "OcamlRts.String.head" [asString a]
mlPrimFn StrTail [a] = pure . mlRepr $ fnCall "OcamlRts.String.tail" [asString a]
mlPrimFn StrIndex [s, i] = pure . mlRepr $ fnCall "OcamlRts.String.get" [asString s, asInt i]
mlPrimFn StrCons [c, s] = pure . mlRepr $ fnCall "OcamlRts.String.cons" [asChar c, asString s]
mlPrimFn StrAppend [a, b] = pure . mlRepr $ binOp "^" (asString a) (asString b)
mlPrimFn StrReverse [a] = pure . mlRepr $ fnCall "OcamlRts.String.reverse" [asString a]
mlPrimFn StrSubstr [offset, len, s] = pure . mlRepr $ fnCall "OcamlRts.String.substring" [asInt offset, asInt len, asString s]
mlPrimFn DoubleExp args = doubleFn "Float.exp" args
mlPrimFn DoubleLog args = doubleFn "Float.log" args
mlPrimFn DoubleSin args = doubleFn "Float.sin" args
mlPrimFn DoubleCos args = doubleFn "Float.cos" args
mlPrimFn DoubleTan args = doubleFn "Float.tan" args
mlPrimFn DoubleASin args = doubleFn "Float.asin" args
mlPrimFn DoubleACos args = doubleFn "Float.acos" args
mlPrimFn DoubleATan args = doubleFn "Float.atan" args
mlPrimFn DoubleSqrt args = doubleFn "Float.sqrt" args
mlPrimFn DoubleFloor args = doubleFn "Float.floor" args
mlPrimFn DoubleCeiling args = doubleFn "Float.ceil" args
mlPrimFn BelieveMe [_, _, x] = pure x
mlPrimFn Crash [_, msg] = pure $ fnCall "raise" [fnCall "Idris2_Exception" [asString msg]]
mlPrimFn (Cast ty IntType) [a] = castToInt ty a
mlPrimFn (Cast ty IntegerType) [a] = castToInteger ty a
mlPrimFn (Cast ty Bits8Type) [a] = castToBits8 ty a
mlPrimFn (Cast ty Bits16Type) [a] = castToBits16 ty a
mlPrimFn (Cast ty Bits32Type) [a] = castToBits32 ty a
mlPrimFn (Cast ty Bits64Type) [a] = castToBits64 ty a
mlPrimFn (Cast ty StringType) [a] = castToString ty a
mlPrimFn (Cast ty DoubleType) [a] = castToDouble ty a
mlPrimFn (Cast IntType CharType) [a] = pure . mlRepr $ fnCall "char_of_int" [asInt a]
mlPrimFn (Cast from to) _ = throw . InternalError $ "Invalid cast " ++ show from ++ " -> " ++ show to
mlPrimFn fn args = throw . InternalError $ "Unsupported primitive function " ++ show fn ++ " with args: " ++ show args

