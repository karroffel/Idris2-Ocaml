||| Compiling of expressions
|||
||| Expressions track their type along with the generated OCaml code.
||| Because OCaml is a statically typed language and some primitive types in
||| Idris map nicely to OCaml it makes sense to keep this information around to
||| only insert the casts that are necessary.
module Ocaml.Expr

import Compiler.ANF
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
mlName (NS ns x) = "ns__" ++ showSep "'" (reverse ns) ++ "_" ++ mlName x
mlName (UN x) = "un__" ++ mlIdent x
mlName (MN x y) = "mn__" ++ mlIdent x ++ "_" ++ show y
mlName (PV x y) = "pat__" ++ mlName x ++ "_" ++ show y
mlName (DN x y) = mlName y
mlName (Nested (i, x) n) = "n__" ++ show i ++ "_" ++ show x ++ "_" ++ mlName n
mlName (CaseBlock x y) = "case__" ++ mlIdent x ++ "_" ++ show y
mlName (WithBlock x y) = "with__" ++ mlIdent x ++ "_" ++ show y
mlName (Resolved x) = "fn__" ++ show x


mlChar : Char -> String
mlChar c = "\'" ++ (okchar c) ++ "\'"
    where
        okchar : Char -> String
        okchar c = if (c >= ' ') && (c /= '\\') && (c /= '"') && (c /= '\'') && (c <= '~')
            then cast c
            else case c of
                '\0' => "\\x00"
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
mlPrimVal : Constant -> Core String
mlPrimVal (I x) = pure . mlRepr $ (show x)
mlPrimVal (BI x) = pure . mlRepr $ fnCall "Z.of_string" [mlString (show x)]
mlPrimVal (B8 x) = pure . mlRepr $ show x
mlPrimVal (B16 x) = pure . mlRepr $ show x
mlPrimVal (B32 x) = pure . mlRepr $ show x
mlPrimVal (B64 x) = pure . mlRepr $ show x ++ "L"
mlPrimVal (Str x) = pure . mlRepr $ mlString x
mlPrimVal (Ch x) = pure . mlRepr $ mlChar x
mlPrimVal (Db x) = pure . mlRepr $ show x
mlPrimVal WorldVal = pure $ mlRepr "()"
mlPrimVal val = throw . InternalError $ "Unsupported primitive value: " ++ show val

||| Generate patterns for constant values
|||
||| Patterns can differ from "value" expressions for some types.
||| The type is also tracked so that the expression to be matched on can be
||| casted accordingly.
mlPrimValPattern : Constant -> Core String
mlPrimValPattern (I x) = pure (show x)
mlPrimValPattern (BI x) = pure (mlString (show x))
mlPrimValPattern (B8 x) = pure (show x)
mlPrimValPattern (B16 x) = pure (show x)
mlPrimValPattern (B32 x) = pure (show x)
mlPrimValPattern (B64 x) = pure (show x ++ "L")
mlPrimValPattern (Str x) = pure (mlString x)
mlPrimValPattern (Ch x) = pure (mlChar x)
mlPrimValPattern (Db x) = pure (show x)
mlPrimValPattern WorldVal = pure ("()")
mlPrimValPattern val = throw . InternalError $ "Unsupported primitive in pattern: " ++ show val


mlBlock : (tag : Int) -> (args : List String) -> String
mlBlock tag args =
    let numArgs = length args
        block = "let block = Obj.new_block " ++ show tag ++ " " ++ show numArgs ++ " in "
        fieldSets = flap ([0..numArgs] `zip` args) \(i, arg) =>
            "Obj.set_field block " ++ show i ++ " " ++ arg ++ ";"
    in "(" ++ block ++ showSep " " fieldSets ++ " block)"


mlVar : AVar -> String
mlVar (ALocal i) = mlVarname i
mlVar ANull = mlRepr "()"

mutual

    ||| Generate code for an expression
    export
    mlExpr : ANF -> Core String
    mlExpr (AV fc var) = pure $ mlVar var
    mlExpr (AAppName fc name []) = do
        let src = fnCall "Lazy.force" [mlName name]
        pure src
    
    mlExpr (AAppName fc name args) = do
        let src = fnCall (mlName name) $ map mlVar args
        pure src
    
    mlExpr (AUnderApp fc name missing args) = do
        let src = fnCall (mlName name) $ map mlVar args
        pure $ mlRepr src
    
    mlExpr (AApp fc closure arg) = do
        let src = fnCall (fnCall "as_fun" [mlVar closure]) [mlVar arg]
        pure src
    
    mlExpr (ALet fc var rhs expr) = do
        rhs' <- mlExpr rhs
        expr' <- mlExpr expr
        let header = "let " ++ mlVarname var ++ " = " ++ rhs' ++ " in "
        pure $ "(" ++ header ++ expr' ++ ")"
    
    mlExpr (ACon fc name Nothing args) = do
        -- type constructor
        let args' = map mlVar args
        let nameField = mlRepr (mlString $ show name)

        pure $ mlBlock 0 $ nameField :: args'
    
    mlExpr (ACon fc name (Just tag) args) = do
        let args' = map mlVar args
        
        pure $ mlBlock tag args'
    
    mlExpr (AOp fc primFn args) = mlPrimFn primFn $ map mlVar args
    
    mlExpr (AExtPrim fc name args) = do
        case !(exPrim name args) of
            Just exp => pure exp

            Nothing => do
                coreLift $ putStrLn $ "Unimplemented ExtPrim!"
                coreLift $ putStrLn $ "ExtPrim: " ++ show name
                coreLift $ putStrLn $ "   args: " ++ show args
                pure $ mlRepr "()"

    mlExpr (AConCase fc var alts def) = do
        let var' = mlVar var
        let header = "match " ++ fnCall "get_tag" [var'] ++ " with "
        
        def' <- the (Core String) $ case def of
            Nothing => pure ""
            Just e => do
                e' <- mlExpr e
                pure $ "| _ -> " ++ e'
                
        let (matchEx, pats, fieldOffset) = case alts of
                (MkAConAlt name Nothing _ _)::_ =>
                    let matchEx = fnCall "as_string" [fnCall "Obj.field" [var', "0"]] in
                    let pats = flap alts \(MkAConAlt name _ _ _) => mlString (show name) in
                    (matchEx, pats, the Nat 1)
                _ =>
                    let matchEx = fnCall "get_tag" [var'] in
                    let pats = flap alts \(MkAConAlt _ tag _ _) => show $ fromMaybe 0 tag in
                    (matchEx, pats, the Nat 0)
        
    
        arms <- for (pats `zip` alts) \(pat, MkAConAlt name tag names e) => do
        
            let numNames = length names

            let binders = flap ([0..numNames] `zip` names) \(i, name) =>
                    "let " ++ mlVarname name ++ " : Obj.t = "
                      ++ fnCall "Obj.field" [var', show (i + fieldOffset)] ++ " in "

            e' <- mlExpr e
            
            pure $ "| " ++ pat ++ " -> " ++ concat binders ++ "(" ++ e' ++ ")"
    
        pure $ "(" ++ header ++ showSep " " arms ++ def' ++ ")"
        
    mlExpr (AConstCase fc var alts def) = do
        let header = "match " ++ fnCall "Obj.obj" [mlVar var] ++ " with "
        
        def' <- case def of
                    Nothing => pure ""
                    Just e => do
                        e' <- mlExpr e
                        pure $ "| _ -> " ++ e'
        
        arms <- for alts \(MkAConstAlt c exp) => do
            pat <- mlPrimValPattern c
            exp' <- mlExpr exp
            pure $ "| " ++ pat ++ " -> (" ++ exp' ++ ")"
        
        pure $ "(" ++ header ++ showSep " " arms ++ def' ++ ")"
    
    mlExpr (APrimVal fc constant) = mlPrimVal constant
    mlExpr (AErased fc) = pure $ mlRepr "()"
    mlExpr (ACrash fc msg) = pure $ "(raise (Idris2_Exception " ++ mlString msg ++ "))"
    
    

    ||| Generate code for external functions
    exPrim : Name ->
             List AVar ->
             Core (Maybe String)
    exPrim name args =
        case (show name, args) of
            ("System.Info.prim__codegen", []) => pure . Just $ mlString "ocaml"
            ("System.Info.prim__os", []) => do
                let call = fnCall "OcamlRts.System.os_name" ["(Obj.magic ())"]
                pure . Just $ mlRepr call

            -- IORef
            ("Data.IORef.prim__newIORef", [_, val, world]) => do
                pure . Just . mlRepr $ fnCall "ref" [mlVar val]
                
            ("Data.IORef.prim__writeIORef", [_, ref, val, world]) => do
                let ref' = fnCall "as_ref" [mlVar ref]
                let src = "(" ++ ref' ++ " := " ++ mlVar val ++ "; Obj.repr ())";
                pure $ Just src
                
            ("Data.IORef.prim__readIORef", [_, ref, world]) => do
                let ref' = fnCall "as_ref" [mlVar ref]
                let src = mlRepr $ "(!" ++ ref' ++ ")"
                pure $ Just src

            -- IOArray
            ("Data.IOArray.Prims.prim__newArray", [_, len, val, world]) => do
                let src = fnCall "Array.make" [asInt $ mlVar len, mlVar val]
                pure . Just . mlRepr $ src
            
            ("Data.IOArray.Prims.prim__arraySet", [_, arr, idx, val, world]) => do
                let call = fnCall "Array.set" [fnCall "as_array" [mlVar arr], asInt $ mlVar idx, mlVar val]
                pure . Just $ "(" ++ call ++ "; Obj.repr ())"
                
            ("Data.IOArray.Prims.prim__arrayGet", [_, arr, idx, world]) => do
                let call = fnCall "Array.get" [fnCall "as_array" [mlVar arr], asInt $ mlVar idx]
                pure . Just . mlRepr $ call

            ("Prelude.Uninhabited.void", [_, _]) => do
                pure . Just . mlRepr $ "()"

            _ => pure Nothing
