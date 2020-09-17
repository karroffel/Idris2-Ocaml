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

import Utils.Hex

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
mlName (NS ns x) = "ns__" ++ showNSWithSep "'" ns ++ "_" ++ mlName x
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


mutual

    ||| Generate code for an expression
    export
    mlExpr : NamedCExp -> Core String
    mlExpr (NmLocal fc name) = pure $ mlName name
    mlExpr (NmRef fc name) = pure $ mlName name
    mlExpr (NmLam fc name rhs) = do
        let name' = mlName name
        rhs' <- mlExpr rhs
        
        pure . mlRepr . parens $ "fun (" ++ name' ++ " : Obj.t) : Obj.t -> " ++ rhs'

    mlExpr (NmLet fc name rhs expr) = do
        rhs' <- mlExpr rhs
        expr' <- mlExpr expr
        
        let header = "let " ++ mlName name ++ " : Obj.t = " ++ rhs' ++ " in "
        let src = header ++ expr'
        pure $ parens src
    
    mlExpr (NmApp fc (NmRef _ name) []) = pure $ fnCall "Lazy.force" [mlName name]
    mlExpr (NmApp fc (NmRef _ name) args) = do
        args' <- traverse mlExpr args
        pure $ fnCall (mlName name) args'
    
    mlExpr (NmApp fc base []) = do
        base' <- mlExpr base
        pure $ fnCall "Lazy.force" [fnCall "as_lazy" [base']]
        
    mlExpr (NmApp fc base args) = do
        base' <- mlExpr base
        args' <- traverse mlExpr args
        let call = fnCall (fnCall "Obj.magic" [base']) args'
        pure $ call
    
    mlExpr (NmCon fc name Nothing args) = do
        let name' = mlRepr . mlString $ show name
        args' <- traverse mlExpr args
        
        pure $ mlBlock 0 (name' :: args')
        
    mlExpr (NmCon fc name (Just tag) []) = pure . mlRepr $ show tag
    mlExpr (NmCon fc name (Just tag) args) = do
        args' <- traverse mlExpr args
        pure $ mlBlock tag args'
    
    mlExpr (NmOp fc fn args) = do
        args' <- traverse mlExpr args
        mlPrimFn fn args'
    
    mlExpr (NmExtPrim fc name args) = do
        args' <- traverse mlExpr args
        case !(exPrim name args') of
            Just exp => pure exp

            Nothing => do
                coreLift $ putStrLn $ "Unimplemented ExtPrim!"
                coreLift $ putStrLn $ "ExtPrim: " ++ show name
                coreLift $ putStrLn $ "   args: " ++ show args
                pure $ mlRepr "()"
    
    mlExpr (NmForce fc expr) = do
        expr' <- mlExpr expr
        pure $ fnCall "Lazy.force" [fnCall "as_lazy" [expr']]
    
    mlExpr (NmDelay fc expr) = do
        expr' <- mlExpr expr
        pure . mlRepr $ fnCall "lazy" [expr']
    
    mlExpr (NmConCase fc expr alts def) = do
        
        expr' <- mlExpr expr
        let matchVal = "let match_val' : Obj.t = " ++ expr' ++ " in "
        
        def' <- the (Core String) $ case def of
            Nothing => pure ""
            Just e => do
                e' <- mlExpr e
                pure $ "| _ -> " ++ e'
                
        let (matchEx, pats, fieldOffset) = case alts of
                (MkNConAlt name Nothing _ _)::_ =>
                    let matchEx = fnCall "as_string" [fnCall "Obj.field" ["match_val'", "0"]] in
                    let pats = flap alts \(MkNConAlt name _ _ _) => mlString (show name) in
                    (matchEx, pats, the Nat 1)
                _ =>
                    let matchEx = fnCall "get_tag" ["match_val'"] in
                    let pats = flap alts \(MkNConAlt _ tag _ _) => show $ fromMaybe 0 tag in
                    (matchEx, pats, the Nat 0)
        
        let header = "match " ++ matchEx ++ " with "
        
        arms <- for (pats `zip` alts) \(pat, MkNConAlt name tag names e) => do
        
            let numNames = length names

            let binders = flap ([0..numNames] `zip` names) \(i, name) =>
                    "let " ++ mlName name ++ " : Obj.t = "
                      ++ fnCall "Obj.field" ["match_val'", show (i + fieldOffset)] ++ " in "

            e' <- mlExpr e
            
            pure $ "| " ++ pat ++ " -> " ++ concat binders ++ parens e'
        
        pure . parens $ matchVal ++ header ++ showSep " " arms ++ def'
    
    mlExpr (NmConstCase fc expr alts def) = do
        let isBigInt = case alts of
                        MkNConstAlt (BI _) _ :: _ => True
                        _ => False
    
        let matchExpr = fnCall "Obj.obj" [!(mlExpr expr)]
        let matchExpr' = if isBigInt
                            then fnCall "Z.to_string" [matchExpr]
                            else matchExpr
        
        let header = "match " ++ matchExpr' ++ " with "
        
        def' <- case def of
                    Nothing => pure ""
                    Just e => do
                        e' <- mlExpr e
                        pure $ "| _ -> " ++ e'
        
        arms <- for alts \(MkNConstAlt c exp) => do
            pat <- mlPrimValPattern c
            exp' <- mlExpr exp
            pure $ "| " ++ pat ++ " -> (" ++ exp' ++ ")"
        
        pure $ "(" ++ header ++ showSep " " arms ++ def' ++ ")"
    
    mlExpr (NmPrimVal fc const) = mlPrimVal const
    mlExpr (NmErased fc) = pure $ mlRepr "()"
    mlExpr (NmCrash fc msg) =
        pure $ fnCall "raise" [fnCall "Idris2_Exception" [mlString msg]]

    ||| Generate code for external functions
    exPrim : Name ->
             List String ->
             Core (Maybe String)
    exPrim name args =
        case (show name, args) of
            ("System.Info.prim__codegen", []) => pure . Just $ mlString "ocaml"
            ("System.Info.prim__os", []) => do
                let call = fnCall "OcamlRts.System.os_name" ["(Obj.magic ())"]
                pure . Just $ mlRepr call

            -- IORef
            ("Data.IORef.prim__newIORef", [_, val, world]) => do
                pure . Just . mlRepr $ fnCall "ref" [val]
                
            ("Data.IORef.prim__writeIORef", [_, ref, val, world]) => do
                let ref' = fnCall "as_ref" [ref]
                let src = "(" ++ ref' ++ " := " ++ val ++ "; Obj.repr ())";
                pure $ Just src
                
            ("Data.IORef.prim__readIORef", [_, ref, world]) => do
                let ref' = fnCall "as_ref" [ref]
                let src = mlRepr $ "(!" ++ ref' ++ ")"
                pure $ Just src

            -- IOArray
            ("Data.IOArray.Prims.prim__newArray", [_, len, val, world]) => do
                let src = fnCall "Array.make" [asInt len, val]
                pure . Just . mlRepr $ src
            
            ("Data.IOArray.Prims.prim__arraySet", [_, arr, idx, val, world]) => do
                let call = fnCall "Array.set" [fnCall "as_array" [arr], asInt idx, val]
                pure . Just $ "(" ++ call ++ "; Obj.repr ())"
                
            ("Data.IOArray.Prims.prim__arrayGet", [_, arr, idx, world]) => do
                let call = fnCall "Array.get" [fnCall "as_array" [arr], asInt idx]
                pure . Just . mlRepr $ call

            ("Prelude.Uninhabited.void", [_, _]) => do
                pure . Just . mlRepr $ "()"

            _ => pure Nothing
