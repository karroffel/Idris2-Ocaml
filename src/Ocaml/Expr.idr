||| Compiling of expressions
|||
||| Expressions track their type along with the generated OCaml code.
||| Because OCaml is a statically typed language and some primitive types in
||| Idris map nicely to OCaml it makes sense to keep this information around to
||| only insert the casts that are necessary.
module Ocaml.Expr

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.List
import Data.Maybe
import Data.NameMap
import Data.Vect

import Debug.Trace

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


||| Compiled OCaml code for an expression, including the `SType`.
|||
||| The generated OCaml code should always have same type as the `type` field.
||| This allows casts to only be inserted when needed.
|||
||| The tracking of types is a small abstract interpretation, only primitive
||| types are supported and everything else is `SOpaque`.
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

||| The name of the OCaml support function that serve as a hint to the OCaml
||| type checker.
|||
||| This is needed when function values (which are represented as `SOpaque`) are
||| called. The type of the arguments are found automatically when using
||| `Obj.magic`, but the return type can't always be inferred.
|||
||| These hint functions act like the Idris function `the type` and only
||| provides a hint.
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

||| The name of OCaml type used to represent values of `SType`s.
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
|||
||| These casts are less "conversion" casts and rather "reinterpret the data"
||| type casts. The values are unchanged and the casts only apply to the types.
export
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
                   

||| Generate OCaml code for constant values
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

||| Generate patterns for constant values
|||
||| Patterns can differ from "value" expressions for some types.
||| The type is also tracked so that the expression to be matched on can be
||| casted accordingly.
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
    ||| Generate code for an expression and cast it if needed
    |||
    ||| If a cast is not needed because the types already match then this
    ||| function behaves the same as `mlExpr`
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
    mlExpr e@(NmLocal fc _) = trace ("Local " ++ show fc) $ mlExpr' e
    mlExpr e@(NmRef fc _) = trace ("Ref " ++ show fc) $ mlExpr' e
    mlExpr e@(NmLam fc _ _) = trace ("Lam " ++ show fc) $ mlExpr' e
    mlExpr e@(NmLet fc _ _ _) = trace ("Let " ++ show fc) $ mlExpr' e
    mlExpr e@(NmApp fc _ _) = trace ("App " ++ show fc) $ mlExpr' e
    mlExpr e@(NmCon fc _ _ _) = trace ("Con " ++ show fc) $ mlExpr' e
    mlExpr e@(NmOp fc _ _) = trace ("Op " ++ show fc) $ mlExpr' e
    mlExpr e@(NmExtPrim fc _ _) = trace ("ExtPrim " ++ show fc) $ mlExpr' e
    mlExpr e@(NmForce fc _) = trace ("Force " ++ show fc) $ mlExpr' e
    mlExpr e@(NmDelay fc _) = trace ("Delay " ++ show fc) $ mlExpr' e
    mlExpr e@(NmConCase fc _ _ _) = trace ("ConCase " ++ show fc) $ mlExpr' e
    mlExpr e@(NmConstCase fc _ _ _) = trace ("ConstCase " ++ show fc) $ mlExpr' e
    mlExpr e@(NmPrimVal fc _) = trace ("PrimVal " ++ show fc) $ mlExpr' e
    mlExpr e@(NmErased fc) = trace ("Erased " ++ show fc) $ mlExpr' e
    mlExpr e@(NmCrash fc _) = trace ("Crash " ++ show fc) $ mlExpr' e



    ||| Generate code for an expression
    export
    mlExpr' : {auto di : DefInfos} ->
            {auto funArgs : NameMap SType } ->
            NamedCExp -> Core MLExpr
    mlExpr' (NmLocal fc x) = do
        let ty = fromMaybe SOpaque (lookup x funArgs)
        let source = mlName x
        pure $ MkMLExpr source ty
    mlExpr' (NmRef fc x) =
        let source = fnCall "as_opaque" [mlName x]
            type = SOpaque
        in pure $ MkMLExpr source type
    mlExpr' (NmLam fc x expr) = do
        expr' <- castedExpr SOpaque expr
        -- functions values are always `SOpaque -> SOpaque`, so a cast is needed
        let source = "(as_opaque (fun (" ++ mlName x ++ " : idr2_opaque) : idr2_opaque -> "
                ++ expr'.source
                ++ "))"
            type = SOpaque
        pure $ MkMLExpr source type
    mlExpr' (NmLet fc x rhs expr) = do
        rhs' <- mlExpr rhs
        -- insert the newly bound name into the type environment for `expr`
        let funArgs' = insert x rhs'.type funArgs
        expr' <- mlExpr {funArgs = funArgs'} expr
        let source = "(let " ++ mlName x ++ " = " ++ rhs'.source ++ " in " ++ expr'.source ++ ")"
        let type = expr'.type
        pure $ MkMLExpr source type
    mlExpr' (NmApp fc (NmRef _ name) args) = do
        -- function call with all arguments supplied
        args' <- traverse mlExpr args
        case lookup name di of
            Just tyInfo => do
                args <- traverse (uncurry castedExpr) (tyInfo.argTypes `zip` args)
                -- functions without any arguments still need a `()`
                let args' = if isNil args then [erased] else args
                let call = fnCall (mlName name) (map source args')
                pure $ MkMLExpr call tyInfo.restType
                
            Nothing => throw $ InternalError ("Unsupported function " ++ show name)

    mlExpr' (NmApp fc base args) = do
        -- function call for a function value, might not have all argument supplied
        base' <- mlExpr base
        args' <- traverse mlExpr args
        -- can't call a function without arguments, needs at least `()`
        let args'' = if isNil args then [erased] else args'

        let src = fnCall "hint_opaque" [fnCall "as_fun" (base'.source :: map source args'')]
            type = SOpaque
        pure $ MkMLExpr src type

    mlExpr' (NmCon fc name tag args) = do
        let tag' = fromMaybe 0 tag
        case lookup name di of
            Just tyInfo => do
                -- if type information is available then generate "optimal" code
                args' <- traverse (uncurry castedExpr) (tyInfo.argTypes `zip` args)
                let argsArray = "(" ++ showSep ", " (map source args') ++ ")"
                    src = "(as_opaque (" ++ show tag' ++ ", as_opaque " ++ argsArray ++ "))"
                pure $ MkMLExpr src SOpaque
            Nothing => do
                args' <- traverse (castedExpr SOpaque) args
                let argsArray = "(" ++ showSep ", " (map source args') ++ ")"
                    src = "(as_opaque (" ++ show tag' ++ ", as_opaque " ++ argsArray ++ "))"
                pure $ MkMLExpr src SOpaque

    mlExpr' (NmOp fc fn args) = do
        res <- mlPrimFn fn args
        args' <- traverse (uncurry castedExpr) $ res.argTypes `zip` args
        let src = res.printer (map source args')
        pure $ MkMLExpr src res.retType

    mlExpr' (NmExtPrim fc name args) =
        case !(exPrim name args) of
            Just exp => pure exp
            
            Nothing => do
                coreLift $ putStrLn $ "Unimplemented ExtPrim!"
                coreLift $ putStrLn $ "ExtPrim: " ++ show name
                coreLift $ putStrLn $ "   args: " ++ show args
                pure erased

    mlExpr' (NmForce fc expr) = do
        expr' <- mlExpr expr
        let src = fnCall "Lazy.force" [fnCall "as_lazy" [expr'.source]]
        pure $ MkMLExpr src SOpaque
    mlExpr' (NmDelay fc expr) = do
        expr' <- mlExpr expr
        let src = fnCall "as_opaque" [fnCall "lazy" [expr'.source]]
        pure $ MkMLExpr src SOpaque
    mlExpr' (NmConCase fc expr alts def) = do
        -- TODO if all alts have the same type then the whole expression
        -- can have the same type too.
        --
        -- Right now all `case` expressions are `SOpaque`.
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

    mlExpr' (NmConstCase fc expr alts def) = do
        -- TODO if all alts have the same type then the whole expression
        -- can have the same type too.
        --
        -- Right now all `case` expressions are `SOpaque`.
        alts' <- traverse alt alts
        def' <- case def of
            Just e => do
                e' <- castedExpr SOpaque e
                pure $ "| _ -> " ++ e'.source
            Nothing => pure ""
        
        let arms = map snd alts'
            constTy = map fst alts'

        -- Try to find the type of the expression by looking at the patterns
        expr' <- case constTy of
                    [] => castedExpr SOpaque expr
                    (t::_) => castedExpr t expr
        
        -- Integers are matched as Strings for now, so add a conversion
        -- TODO make this a bit nicer
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

    mlExpr' (NmPrimVal fc val) = mlPrimVal val
    mlExpr' (NmErased fc) = pure erased
    mlExpr' (NmCrash fc x) = 
        let source = fnCall "raise" [fnCall "Idris2_Exception" [mlString $ show x]]
            type = SOpaque
        in pure $ MkMLExpr source type

    ||| Generate code for external functions
    exPrim : {auto di : DefInfos} ->
             {auto funArgs : NameMap SType } ->
             Name ->
             List NamedCExp ->
             Core (Maybe MLExpr)
    exPrim name args =
        case (show name, args) of
            ("System.Info.prim__codegen", []) => pure . Just $ MkMLExpr (mlString "ocaml") SString
            ("System.Info.prim__os", []) => do
                pure . Just $ MkMLExpr "(OcamlRts.System.os_name (Obj.magic ()))" SString
            
            -- IORef
            ("Data.IORef.prim__newIORef", [_, val, world]) => do
                val' <- castedExpr SOpaque val
                let src = "(as_opaque (ref " ++ val'.source ++ "))"
                pure . Just $ MkMLExpr src SOpaque
            ("Data.IORef.prim__writeIORef", [_, ref, val, world]) => do
                ref' <- castedExpr SOpaque ref
                val' <- castedExpr SOpaque val
                let src = "((as_ref (" ++ ref'.source ++ ")) := " ++ val'.source ++ "; as_opaque ())"
                pure . Just $ MkMLExpr src SOpaque
            ("Data.IORef.prim__readIORef", [_, ref, world]) => do
                ref' <- castedExpr SOpaque ref
                let src = "(as_opaque (!(as_ref " ++ ref'.source ++ ")))"
                pure . Just $ MkMLExpr src SOpaque

            -- IOArray
            ("Data.IOArray.Prims.prim__newArray", [_, len, val, world]) => do
                len' <- castedExpr SInt len
                val' <- castedExpr SOpaque val
                let src = "(as_opaque (Array.make " ++ len'.source ++ " " ++ val'.source ++ "))"
                pure . Just $ MkMLExpr src SOpaque
            ("Data.IOArray.Prims.prim__arraySet", [_, arr, idx, val, world]) => do
                arr' <- castedExpr SOpaque arr
                idx' <- castedExpr SInt idx
                val' <- castedExpr SOpaque val
                let src = "(Array.set (as_array " ++ arr'.source ++ ") " ++ idx'.source ++ " " ++ val'.source ++ "; as_opaque ())"
                pure . Just $ MkMLExpr src SOpaque
            ("Data.IOArray.Prims.prim__arrayGet", [_, arr, idx, world]) => do
                arr' <- castedExpr SOpaque arr
                idx' <- castedExpr SInt idx
                let src = "(as_opaque (Array.get (as_array " ++ arr'.source ++ ") " ++ idx'.source ++ "))"
                pure . Just $ MkMLExpr src SOpaque

            ("Prelude.Uninhabited.void", [_, _]) => do
                pure . Just $ MkMLExpr "(as_opaque ())" SOpaque
            
            _ => pure Nothing