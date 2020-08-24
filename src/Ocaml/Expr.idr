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
mlName (NS xs x) = "ns__" ++ showSep "'" (reverse xs) ++ "_" ++ mlName x
mlName (UN x) = "un__" ++ mlIdent x
mlName (MN x y) = "mn__" ++ mlIdent x ++ "_" ++ show y
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

public export
erased : MLExpr
erased = MkMLExpr "()" SErased

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
ocamlTypeName SInteger = "Z.t"
ocamlTypeName SBits8 = "int"
ocamlTypeName SBits16 = "int"
ocamlTypeName SBits32 = "int"
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

mlChar : Char -> String
mlChar c = "\'" ++ (okchar c) ++ "\'" 
    where
        okchar : Char -> String
        okchar c = if (c >= ' ') && (c /= '\\') && (c /= '"') && (c /= '\'') && (c <= '~')
            then cast c
            else case c of
                '\0' => "\\0"
                '\'' => "\\'"
                '"' => "\\\""
                '\r' => "\\r"
                '\n' => "\\n"
                '\t' => "\\t"
                '\b' => "\\b"
                other => "\\x" ++ leftPad '0' 2 (asHex (cast {to=Int} c))

mlString : String -> String
mlString s = "\"" ++ (concatMap okchar (unpack s)) ++ "\""
    where
    okchar : Char -> String
    okchar c = if (c >= ' ') && (c /= '\\') && (c /= '"') && (c /= '\'') && (c <= '~')
                    then cast c
                    else case c of
                            '\0' => "\\0"
                            '\'' => "\\'"
                            '"' => "\\\""
                            '\r' => "\\r"
                            '\n' => "\\n"
                            '\t' => "\\t"
                            '\b' => "\\b"
                            other => "\\u{" ++ asHex (cast {to=Int} c) ++ "}"



binOp : (op : String) -> (a, b : String) -> String
binOp op a b = "(" ++ a ++ " " ++ op ++ " " ++ b ++ ")"

fnCall : (fn : String) -> (args : List String) -> String
fnCall fn args = "(" ++ fn ++ " " ++ showSep " " args ++ ")"

boolOp : (op : String) -> (a, b : String) -> String
boolOp op a b = fnCall "int_of_bool" [binOp op a b]
                            


mlPrimVal : Constant -> Core MLExpr
mlPrimVal (I x) = pure $ MkMLExpr (show x) SInt
mlPrimVal (BI x) = pure $ MkMLExpr (fnCall "Z.of_string" [mlString (show x)]) SInteger
mlPrimVal (B8 x) = pure $ MkMLExpr (show x) SBits8
mlPrimVal (B16 x) = pure $ MkMLExpr (show x) SBits16
mlPrimVal (B32 x) = pure $ MkMLExpr (show x) SBits32
mlPrimVal (B64 x) = pure $ MkMLExpr (show x ++ "L") SBits64
mlPrimVal (Str x) = pure $ MkMLExpr (mlString x) SString
mlPrimVal (Ch x) = pure $ MkMLExpr (mlChar x) SChar
mlPrimVal (Db x) = pure $ MkMLExpr (show x) SDouble
mlPrimVal WorldVal = pure $ MkMLExpr "()" SWorld
mlPrimVal val = throw . InternalError $ "Unsupported primitive value: " ++ show val

mlPrimValPattern : Constant -> Core (String, SType)
mlPrimValPattern (I x) = pure (show x, SInt)
mlPrimValPattern (BI x) = pure (mlString (show x), SInteger)
mlPrimValPattern (B8 x) = pure (show x, SBits8)
mlPrimValPattern (B16 x) = pure (show x, SBits16)
mlPrimValPattern (B32 x) = pure (show x, SBits32)
mlPrimValPattern (B64 x) = pure (show x ++ "L", SBits64)
mlPrimValPattern (Str x) = pure (mlString x, SString)
mlPrimValPattern (Ch x) = pure (mlChar x, SChar)
mlPrimValPattern (Db x) = pure (show x, SDouble)
mlPrimValPattern WorldVal = pure ("()", SWorld)
mlPrimValPattern val = throw . InternalError $ "Unsupported primitive in pattern: " ++ show val


record PrimFnRes (arity : Nat) where
    constructor MkPrimFnRes
    argTypes : Vect arity SType
    retType : SType
    printer : Vect arity String -> String

binaryPrimFn : {arity : Nat} -> SType -> (Vect arity String -> String) -> Core (PrimFnRes arity)
binaryPrimFn ty fn = pure $ MkPrimFnRes (replicate arity ty) ty fn

mlPrimFn : PrimFn arity -> Vect arity NamedCExp -> Core (PrimFnRes arity)
mlPrimFn (Add IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "+" a b
mlPrimFn (Add IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.add" [a, b]
mlPrimFn (Add Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => binOp "+" a b
mlPrimFn (Add Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => binOp "+" a b
mlPrimFn (Add Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => binOp "+" a b
mlPrimFn (Add Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.add" [a, b]
mlPrimFn (Add DoubleType) [a, b] = binaryPrimFn SDouble $ \[a, b] => binOp "+." a b
mlPrimFn (Sub IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "-" a b
mlPrimFn (Sub IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.sub" [a, b]
mlPrimFn (Sub Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => binOp "-" a b
mlPrimFn (Sub Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => binOp "-" a b
mlPrimFn (Sub Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => binOp "-" a b
mlPrimFn (Sub Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.sub" [a, b]
mlPrimFn (Sub DoubleType) [a, b] = binaryPrimFn SDouble $ \[a, b] => binOp "-." a b
mlPrimFn (Mul IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "*" a b
mlPrimFn (Mul IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.mul" [a, b]
mlPrimFn (Mul Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => binOp "*" a b
mlPrimFn (Mul Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => binOp "*" a b
mlPrimFn (Mul Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => binOp "*" a b
mlPrimFn (Mul Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.mul" [a, b]
mlPrimFn (Mul DoubleType) [a, b] = binaryPrimFn SDouble $ \[a, b] => binOp "*." a b
mlPrimFn (Div IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "/" a b
mlPrimFn (Div IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.div" [a, b]
mlPrimFn (Div Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => binOp "/" a b
mlPrimFn (Div Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => binOp "/" a b
mlPrimFn (Div Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => binOp "/" a b
mlPrimFn (Div Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.unsigned_div" [a, b]
mlPrimFn (Div DoubleType) [a, b] = binaryPrimFn SDouble $ \[a, b] => binOp "/." a b
mlPrimFn (Mod IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "mod" a b
mlPrimFn (Mod IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.rem" [a, b]
mlPrimFn (Mod Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => binOp "mod" a b
mlPrimFn (Mod Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => binOp "mod" a b
mlPrimFn (Mod Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => binOp "mod" a b
mlPrimFn (Mod Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.unsigned_rem" [a, b]
mlPrimFn (Neg IntType) [a] = pure $ MkPrimFnRes [SInt] SInt $ \[a] => fnCall "-" [a]
mlPrimFn (Neg IntegerType) [a] = pure $ MkPrimFnRes [SInteger] SInteger $ \[a] => fnCall "Z.neg" [a]
mlPrimFn (Neg DoubleType) [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "-." [a]
mlPrimFn (ShiftL IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "lsl" a b
mlPrimFn (ShiftL IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.shift_left" [a, fnCall "Z.to_int" [b]]
mlPrimFn (ShiftL Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => binOp "lsl" a b
mlPrimFn (ShiftL Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => binOp "lsl" a b
mlPrimFn (ShiftL Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => binOp "lsl" a b
mlPrimFn (ShiftL Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.shift_left" [a, fnCall "Int64.to_int" [b]]
mlPrimFn (ShiftR IntType) [a, b] = binaryPrimFn SInt $ \[a, b] => binOp "lsr" a b
mlPrimFn (ShiftR IntegerType) [a, b] = binaryPrimFn SInteger $ \[a, b] => fnCall "Z.shift_right" [a, fnCall "Z.to_int" [b]]
mlPrimFn (ShiftR Bits8Type) [a, b] = binaryPrimFn SBits8 $ \[a, b] => binOp "lsr" a b
mlPrimFn (ShiftR Bits16Type) [a, b] = binaryPrimFn SBits16 $ \[a, b] => binOp "lsr" a b
mlPrimFn (ShiftR Bits32Type) [a, b] = binaryPrimFn SBits32 $ \[a, b] => binOp "lsr" a b
mlPrimFn (ShiftR Bits64Type) [a, b] = binaryPrimFn SBits64 $ \[a, b] => fnCall "Int64.shift_right" [a, fnCall "Int64.to_int" [b]]
mlPrimFn (BAnd ty) args = throw $ InternalError "unimplemented bitwise-and"
mlPrimFn (BOr ty) args = throw $ InternalError "unimplemented bitwise-or"
mlPrimFn (BXOr ty) args = throw $ InternalError "unimplemented bitwise-xor"
mlPrimFn (LT ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp "<" a b
mlPrimFn (LTE ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp "<=" a b
mlPrimFn (EQ ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp "==" a b
mlPrimFn (GTE ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp ">=" a b
mlPrimFn (GT ty) [a, b] = let t = stypeFromConst ty in pure $ MkPrimFnRes [t, t] SInt $ \[a, b] => boolOp ">" a b
mlPrimFn StrLength [a] = pure $ MkPrimFnRes [SString] SInt $ \[a] => fnCall "String.length" [a]
mlPrimFn StrHead [a] = pure $ MkPrimFnRes [SString] SChar $ \[a] => fnCall "string_head" [a]
mlPrimFn StrTail [a] = pure $ MkPrimFnRes [SString] SString $ \[a] => fnCall "string_tail" [a]
mlPrimFn StrIndex [s, i] = pure $ MkPrimFnRes [SString, SInt] SChar $ \[a, i] => fnCall "String.get" [a, i]
mlPrimFn StrCons [c, s] = pure $ MkPrimFnRes [SChar, SString] SString $ \[c, s] => fnCall "string_cons" [c, s]
mlPrimFn StrAppend [a, b] = pure $ MkPrimFnRes [SString, SString] SString $ \[a, b] => binOp "^" a b
mlPrimFn StrReverse [a] = pure $ MkPrimFnRes [SString] SString $ \[a] => fnCall "string_reverse" [a]
mlPrimFn StrSubstr [offset, len, s] = pure $ MkPrimFnRes [SInt, SInt, SString] SString $ \[offset, len, s] => fnCall "String.sub" [s, offset, len]
mlPrimFn DoubleExp [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.exp" [a]
mlPrimFn DoubleLog [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.log" [a]
mlPrimFn DoubleSin [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.sin" [a]
mlPrimFn DoubleCos [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.cos" [a]
mlPrimFn DoubleTan [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.tan" [a]
mlPrimFn DoubleASin [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.asin" [a]
mlPrimFn DoubleACos [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.acos" [a]
mlPrimFn DoubleATan [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.atan" [a]
mlPrimFn DoubleSqrt [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.sqrt" [a]
mlPrimFn DoubleFloor [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.floor" [a]
mlPrimFn DoubleCeiling [a] = pure $ MkPrimFnRes [SDouble] SDouble $ \[a] => fnCall "Float.ceil" [a]
mlPrimFn BelieveMe [_, _, x] = pure $ MkPrimFnRes [SErased, SErased, SOpaque] SOpaque $ \[_, _, x] => x
mlPrimFn Crash [_, msg] = pure $ MkPrimFnRes [SErased, SErased] SOpaque $ \[_, _] => fnCall "raise" [fnCall "Idris2_Exception" [show msg]]
-- to Int
mlPrimFn (Cast IntegerType IntType) [a] = pure $ MkPrimFnRes [SInteger] SInt $ \[a] => fnCall "Z.to_int" [a]
mlPrimFn (Cast Bits8Type IntType) [a] = pure $ MkPrimFnRes [SBits8] SInt $ \[a] => a
mlPrimFn (Cast Bits16Type IntType) [a] = pure $ MkPrimFnRes [SBits16] SInt $ \[a] => a
mlPrimFn (Cast Bits32Type IntType) [a] = pure $ MkPrimFnRes [SBits32] SInt $ \[a] => a
mlPrimFn (Cast DoubleType IntType) [a] = pure $ MkPrimFnRes [SDouble] SInt $ \[a] => fnCall "int_of_float" [a]
mlPrimFn (Cast StringType IntType) [a] = pure $ MkPrimFnRes [SString] SInt $ \[a] => fnCall "int_of_string" [a]
mlPrimFn (Cast CharType IntType) [a] = pure $ MkPrimFnRes [SChar] SInt $ \[a] => fnCall "int_of_char" [a]
-- to Integer
mlPrimFn (Cast IntType IntegerType) [a] = pure $ MkPrimFnRes [SInt] SInteger $ \[a] => fnCall "Z.of_int" [a]
mlPrimFn (Cast Bits8Type IntegerType) [a] = pure $ MkPrimFnRes [SBits8] SInteger $ \[a] => fnCall "Z.of_int" [a]
mlPrimFn (Cast Bits16Type IntegerType) [a] = pure $ MkPrimFnRes [SBits16] SInteger $ \[a] => fnCall "Z.of_int" [a]
mlPrimFn (Cast Bits32Type IntegerType) [a] = pure $ MkPrimFnRes [SBits32] SInteger $ \[a] => fnCall "Z.of_int" [a]
mlPrimFn (Cast Bits64Type IntegerType) [a] = pure $ MkPrimFnRes [SBits64] SInteger $ \[a] => fnCall "Z.of_int64" [a]
mlPrimFn (Cast DoubleType IntegerType) [a] = pure $ MkPrimFnRes [SDouble] SInteger $ \[a] => fnCall "Z.of_float" [a]
mlPrimFn (Cast CharType IntegerType) [a] = pure $ MkPrimFnRes [SChar] SInteger $ \[a] => fnCall "Z.of_int" [fnCall "int_of_char" [a]]
mlPrimFn (Cast StringType IntegerType) [a] = pure $ MkPrimFnRes [SString] SInteger $ \[a] => fnCall "Z.of_string" [a]
-- to Bits8
mlPrimFn (Cast IntType Bits8Type) [a] = pure $ MkPrimFnRes [SInt] SBits8 $ \[a] => a
mlPrimFn (Cast IntegerType Bits8Type) [a] = pure $ MkPrimFnRes [SInteger] SBits8 $ \[a] => fnCall "Z.to_int" [a]
mlPrimFn (Cast Bits16Type Bits8Type) [a] = pure $ MkPrimFnRes [SBits16] SBits8 $ \[a] => a -- TODO handle overflow
mlPrimFn (Cast Bits32Type Bits8Type) [a] = pure $ MkPrimFnRes [SBits32] SBits8 $ \[a] => a -- TODO handle overflow
mlPrimFn (Cast Bits64Type Bits8Type) [a] = pure $ MkPrimFnRes [SBits64] SBits8 $ \[a] => fnCall "Int64.to_int" [a]
-- to Bits16
mlPrimFn (Cast IntType Bits16Type) [a] = pure $ MkPrimFnRes [SInt] SBits16 $ \[a] => a -- TODO handle overflow
mlPrimFn (Cast IntegerType Bits16Type) [a] = pure $ MkPrimFnRes [SInteger] SBits16 $ \[a] => fnCall "Z.to_int" [a]
mlPrimFn (Cast Bits8Type Bits16Type) [a] = pure $ MkPrimFnRes [SBits8] SBits16 $ \[a] => a
mlPrimFn (Cast Bits32Type Bits16Type) [a] = pure $ MkPrimFnRes [SBits32] SBits16 $ \[a] => a -- TODO handle overflow
mlPrimFn (Cast Bits64Type Bits16Type) [a] = pure $ MkPrimFnRes [SBits64] SBits16 $ \[a] => fnCall "Int64.to_int" [a] -- TODO handle overflow
-- to Bits32
mlPrimFn (Cast IntType Bits32Type) [a] = pure $ MkPrimFnRes [SInt] SBits32 $ \[a] => a
mlPrimFn (Cast IntegerType Bits32Type) [a] = pure $ MkPrimFnRes [SInteger] SBits32 $ \[a] => fnCall "Z.to_int" [a]
mlPrimFn (Cast Bits8Type Bits32Type) [a] = pure $ MkPrimFnRes [SBits8] SBits32 $ \[a] => a
mlPrimFn (Cast Bits16Type Bits32Type) [a] = pure $ MkPrimFnRes [SBits16] SBits32 $ \[a] => a
mlPrimFn (Cast Bits64Type Bits32Type) [a] = pure $ MkPrimFnRes [SBits64] SBits32 $ \[a] => fnCall "Int64.to_int" [a]
-- to Bits64
mlPrimFn (Cast IntType Bits64Type) [a] = pure $ MkPrimFnRes [SInt] SBits64 $ \[a] => fnCall "Int64.of_int" [a]
mlPrimFn (Cast IntegerType Bits64Type) [a] = pure $ MkPrimFnRes [SInteger] SBits64 $ \[a] => fnCall "Z.of_int" [a] -- TODO handle overflow
mlPrimFn (Cast Bits8Type Bits64Type) [a] = pure $ MkPrimFnRes [SBits8] SBits64 $ \[a] => fnCall "Int64.of_int" [a]
mlPrimFn (Cast Bits16Type Bits64Type) [a] = pure $ MkPrimFnRes [SBits16] SBits64 $ \[a] => fnCall "Int64.of_int" [a]
mlPrimFn (Cast Bits32Type Bits64Type) [a] = pure $ MkPrimFnRes [SBits32] SBits64 $ \[a] => fnCall "Int64.of_int" [a]
-- to String
mlPrimFn (Cast IntType StringType) [a] = pure $ MkPrimFnRes [SInt] SString $ \[a] => fnCall "string_of_int" [a]
mlPrimFn (Cast IntegerType StringType) [a] = pure $ MkPrimFnRes [SInteger] SString $ \[a] => fnCall "Z.to_string" [a]
mlPrimFn (Cast Bits8Type StringType) [a] = pure $ MkPrimFnRes [SBits8] SString $ \[a] => fnCall "string_of_int" [a]
mlPrimFn (Cast Bits16Type StringType) [a] = pure $ MkPrimFnRes [SBits16] SString $ \[a] => fnCall "string_of_int" [a]
mlPrimFn (Cast Bits32Type StringType) [a] = pure $ MkPrimFnRes [SBits32] SString $ \[a] => fnCall "string_of_int" [a]
mlPrimFn (Cast Bits64Type StringType) [a] = pure $ MkPrimFnRes [SBits64] SString $ \[a] => fnCall "Int64.to_string" [a]
mlPrimFn (Cast DoubleType StringType) [a] = pure $ MkPrimFnRes [SDouble] SString $ \[a] => fnCall "string_of_float" [a]
mlPrimFn (Cast CharType StringType) [a] = pure $ MkPrimFnRes [SChar] SString $ \[a] => fnCall "String.make" ["1", a]
-- to Double
mlPrimFn (Cast IntType DoubleType) [a] = pure $ MkPrimFnRes [SInt] SDouble $ \[a] => fnCall "float_of_int" [a]
mlPrimFn (Cast IntegerType DoubleType) [a] = pure $ MkPrimFnRes [SInteger] SDouble $ \[a] => fnCall "Z.to_float" [a]
mlPrimFn (Cast StringType DoubleType) [a] = pure $ MkPrimFnRes [SString] SDouble $ \[a] => fnCall "float_of_string" [a]
-- to char
mlPrimFn (Cast IntType CharType) [a] = pure $ MkPrimFnRes [SInt] SChar $ \[a] => fnCall "char_of_int" [a]
mlPrimFn (Cast from to) _ = throw . InternalError $ "Invalid cast " ++ show from ++ " -> " ++ show to
mlPrimFn fn args = throw . InternalError $ "Unsupported primitive function " ++ show fn ++ " with args: " ++ show args


mutual
    export
    castedExpr : {auto di : DefInfos} ->
                 {auto funArgs : NameMap SType } ->
                 SType ->
                 NamedCExp ->
                 Core MLExpr
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
        expr' <- castedExpr SOpaque expr
        let source = "(as_opaque (fun (" ++ mlName x ++ " : idr2_opaque) : idr2_opaque -> "
                ++ expr'.source
                ++ "))"
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
                let args' = if isNil args then [erased] else args
                let call = fnCall (mlName name) (map source args')
                pure $ MkMLExpr call tyInfo.restType
                
            Nothing => throw $ InternalError ("Unsupported function " ++ show name)

    mlExpr (NmApp fc base args) = do
        base' <- mlExpr base
        args' <- traverse mlExpr args
        let args'' = if isNil args then [erased] else args'

        let src = fnCall "hint_opaque" [fnCall "as_fun" (base'.source :: map source args'')]
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

    mlExpr (NmExtPrim fc name args) = do
        coreLift $ putStrLn $ "ExtPrim: " ++ show name
        coreLift $ putStrLn $ "   args: " ++ show args
        pure empty -- ?mlExpr_rhs_8
    mlExpr (NmForce fc expr) = do
        expr' <- mlExpr expr
        let src = fnCall "Lazy.force" [fnCall "as_lazy" [expr'.source]]
        pure $ MkMLExpr src SOpaque
    mlExpr (NmDelay fc expr) = do
        expr' <- mlExpr expr
        let src = fnCall "as_opaque" [fnCall "lazy" [expr'.source]]
        pure $ MkMLExpr src SOpaque
    mlExpr (NmConCase fc expr alts def) = do
        expr' <- mlExpr expr
        alts' <- traverse alt alts
        def' <- case def of
            Just e => do
                e' <- castedExpr SOpaque e
                pure $ "| _ -> " ++ e'.source
            Nothing => pure ""
        let src = "(match (as_variant " ++ expr'.source ++ ") with " ++ showSep " " alts' ++ def' ++ ")"
        pure $ MkMLExpr src SOpaque
        where
            alt : {auto di : DefInfos} ->
                  {auto funArgs : NameMap SType } ->
                  NamedConAlt ->
                  Core String
            alt (MkNConAlt name tag names expr) = do
                let numNames = length names
                let tag' = fromMaybe 0 tag
                let src = "| (" ++ show tag' ++ ", fields') -> "
                case lookup name di of
                    Just info => do
                        let fieldTypes = filter (/= SErased) info.argTypes
                            ty = showSep " * " (map ocamlTypeName fieldTypes)
                            ty' = case numNames of
                                0 => "unit"
                                1 => ty
                                _ => "(" ++ ty ++ ")"
                            pat = showSep ", " (map mlName names)
                            pat' = if numNames == 1 then pat else "(" ++ pat ++ ")"
                            binds = "let " ++ pat' ++ " : " ++ ty' ++ " = Obj.magic fields' in "
                            funArgs' = fromList (names `zip` fieldTypes)
                            
                        expr' <- castedExpr {di=di} {funArgs = funArgs `mergeLeft` funArgs'} SOpaque expr
                        pure (src ++ binds ++ expr'.source)
                    Nothing => do
                        let len = length names
                            fieldTypes = replicate len SOpaque
                            ty = showSep " * " (map ocamlTypeName fieldTypes)
                            ty' = case numNames of
                                0 => "unit"
                                1 => ty
                                _ => "(" ++ ty ++ ")"
                            pat = showSep ", " (map mlName names)
                            pat' = if numNames == 1 then pat else "(" ++ pat ++ ")"
                            binds = "let " ++ pat' ++ " : " ++ ty' ++ " = Obj.magic fields' in "
                            funArgs' = fromList (names `zip` fieldTypes)

                        expr' <- castedExpr {di=di} {funArgs = funArgs `mergeLeft` funArgs'} SOpaque expr
                        pure (src ++ binds ++ expr'.source)

    mlExpr (NmConstCase fc expr alts def) = do
        alts' <- traverse alt alts
        def' <- case def of
            Just e => do
                e' <- castedExpr SOpaque e
                pure $ "| _ -> " ++ e'.source
            Nothing => pure ""
        
        let arms = map snd alts'
            constTy = map fst alts'

        expr' <- case constTy of
                    [] => castedExpr SOpaque expr
                    (t::_) => castedExpr t expr
        
        let matchExpr = if expr'.type == SInteger
                            then fnCall "Z.to_string" [expr'.source]
                            else expr'.source

        let src = "(match " ++ matchExpr ++ " with " ++ showSep " " arms ++ def' ++ ")"
        pure $ MkMLExpr src SOpaque
        where
            alt : {auto di : DefInfos} ->
                {auto funArgs : NameMap SType } ->
                NamedConstAlt ->
                Core (SType, String)
            alt (MkNConstAlt const expr) = do
                (pat, ty) <- mlPrimValPattern const
                expr' <- castedExpr {di=di} {funArgs=funArgs} SOpaque expr
                let src = "| " ++ pat ++ " -> " ++ expr'.source
                pure $ (ty, src)

    mlExpr (NmPrimVal fc val) = mlPrimVal val
    mlExpr (NmErased fc) = pure erased
    mlExpr (NmCrash fc x) = 
        let source = fnCall "raise" [fnCall "Idris2_Exception" [show x]]
            type = SOpaque
        in pure $ MkMLExpr source type

