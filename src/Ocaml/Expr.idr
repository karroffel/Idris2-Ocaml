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
import Ocaml.PrimFns
import Ocaml.Utils
import Ocaml.Foreign


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

    mlExpr (NmExtPrim fc name args) =
        case !(exPrim name args) of
            Just exp => pure exp
            
            Nothing => do
                coreLift $ putStrLn $ "Unimplemented ExtPrim!"
                coreLift $ putStrLn $ "ExtPrim: " ++ show name
                coreLift $ putStrLn $ "   args: " ++ show args
                pure empty

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
                        let ty = showSep " * " (map ocamlTypeName info.argTypes)
                            ty' = case numNames of
                                0 => "unit"
                                1 => ty
                                _ => "(" ++ ty ++ ")"
                            pat = showSep ", " (map mlName names)
                            pat' = if numNames == 1 then pat else "(" ++ pat ++ ")"
                            binds = "let " ++ pat' ++ " : " ++ ty' ++ " = Obj.magic fields' in "
                            funArgs' = fromList (names `zip` info.argTypes)
                            
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

    exPrim : {auto di : DefInfos} ->
             {auto funArgs : NameMap SType } ->
             Name ->
             List NamedCExp ->
             Core (Maybe MLExpr)
    exPrim name args =
        case (show name, args) of
            ("System.Info.prim__os", []) => do
                pure . Just $ MkMLExpr "(idr2_sys_os ())" SString
            _ => pure Nothing