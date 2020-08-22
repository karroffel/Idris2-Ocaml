module Ocaml.Expr

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.List
import Data.Maybe
import Data.NameMap

import Utils.Hex

import Ocaml.DefInfo

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
            Just fn =>
                let src = "(" ++ fn ++ " " ++ expr'.source ++ ")"
                in pure $ MkMLExpr src ty

    export
    mlExpr : {auto di : DefInfos} ->
            {auto funArgs : NameMap SType } ->
            NamedCExp -> Core MLExpr
    mlExpr (NmLocal fc x) = do
        let ty = fromMaybe SOpaque (lookup x funArgs)
        let source = mlName x
        pure $ MkMLExpr source ty
    mlExpr (NmRef fc x) =
        let source = "(as_opaque " ++ mlName x ++ ")"
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
                
                let args = tyInfo.argTypes `zip` args

                args' <- traverse (uncurry castedExpr) args

                let call = "(" ++ mlName name ++ " " ++ showSep " " (map source args') ++ ")"

                pure $ MkMLExpr call tyInfo.restType
                
            Nothing => throw $ InternalError ("Unsupported function " ++ show name)

    mlExpr (NmApp fc base args) = do
        base' <- mlExpr base
        args' <- traverse mlExpr args

        let src = "(as_opaque (as_fun " ++ base'.source ++ " " ++ showSep " " (map source args') ++ "))"
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

    mlExpr (NmOp fc x xs) = pure empty --?mlExpr_rhs_7
    mlExpr (NmExtPrim fc p xs) = pure empty --?mlExpr_rhs_8
    mlExpr (NmForce fc x) = pure empty --?mlExpr_rhs_9
    mlExpr (NmDelay fc x) = pure empty --?mlExpr_rhs_10
    mlExpr (NmConCase fc sc xs x) = pure empty --?mlExpr_rhs_11
    mlExpr (NmConstCase fc sc xs x) = pure empty --?mlExpr_rhs_12
    mlExpr (NmPrimVal fc x) = pure empty --?mlExpr_rhs_13
    mlExpr (NmErased fc) = pure empty --?mlExpr_rhs_14
    mlExpr (NmCrash fc x) = 
        let source = "(raise (Idris2_Exception " ++ show x ++ "))"
            type = SOpaque
        in pure $ MkMLExpr source type

