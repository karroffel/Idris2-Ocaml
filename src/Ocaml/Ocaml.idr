module Ocaml.Ocaml

import Idris.Driver

import Compiler.Common
import Compiler.CompileExpr

import Core.Context
import Core.Directory

import Utils.Path
import Utils.Hex

import Data.List
import Data.NameMap
import Data.Maybe
import Data.Vect


import System
import System.File



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

binderInner : Binder ty -> ty
binderInner (Lam x y z) = z
binderInner (Let x val y) = y
binderInner (Pi x y z) = z
binderInner (PVar x y z) = z
binderInner (PLet x val y) = y
binderInner (PVTy x y) = y

findTypes : (names : List Name) ->
            Term names ->
            -- arguments, return type
            (List (ns : List Name ** Term ns), (ns : List Name ** Term ns))
findTypes names (Bind fc x b scope) =
    let inner       = binderInner b
        (rest, ret) = findTypes (x::names) scope
    in ((names ** inner) :: rest, ret)
findTypes names x                   = ([], (names ** x))

printTypeInfo : Context -> Name -> NamedDef -> Core ()
printTypeInfo ctxt name (MkNmFun args y) = do

    Just glob <- lookupCtxtExact name ctxt
    | Nothing => pure ()

    let (argTys, retTy) = findTypes [] glob.type
        argTys' = map (\(_ ** x) => show x) argTys
        retTy'  = show (snd retTy)

    coreLift $ putStrLn $ "Fun Name            " ++ show name
    coreLift $ putStrLn $ "  Arg types         " ++ show argTys'
    coreLift $ putStrLn $ "  Ret type          " ++ show retTy'


    -- coreLift $ putStrLn $ "   Type              " ++ show (glob.type)
    coreLift $ putStrLn $ "     Erase args      " ++ show (glob.eraseArgs)
    coreLift $ putStrLn $ "     Safe erase args " ++ show (glob.safeErase)
    -- coreLift $ putStrLn $ "     Spec args       " ++ show (glob.specArgs)
    coreLift $ putStrLn $ "     Inferrable args " ++ show (glob.inferrable)
    coreLift $ putStrLn ""

    pure ()
    
printTypeInfo ctxt name (MkNmCon tag arity nt) = do
    coreLift $ putStrLn $ "Con Name     " ++ show name
    Just glob <- lookupCtxtExact name ctxt
        | Nothing => coreLift $ putStrLn "Could not get GlobalDef"
    let ty = type glob
    coreLift $ putStrLn $ "  Type: " ++ show ty
printTypeInfo ctxt name (MkNmForeign ccs fargs y) = do
    coreLift $ putStrLn $ "Foreign Name " ++ show name
    Just glob <- lookupCtxtExact name ctxt
        | Nothing => coreLift $ putStrLn "Could not get GlobalDef"
    let ty = type glob
    coreLift $ putStrLn $ "  Type: " ++ show ty
printTypeInfo ctxt name (MkNmError y) = do
    coreLift $ putStrLn $ "Error Name   " ++ show name
    Just glob <- lookupCtxtExact name ctxt
        | Nothing => coreLift $ putStrLn "Could not get GlobalDef"
    let ty = type glob
    coreLift $ putStrLn $ "  Type: " ++ show ty

||| OCaml implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
    ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile = do
    cData <- getCompileData Cases tm
    let ndefs = namedDefs cData
    let ctm = forget (mainExpr cData)

    defs <- get Ctxt
    let context = gamma defs

    _ <- traverse (\(name, _, def) => printTypeInfo context name def) ndefs

    -- funcs <- traverse (\(name, _, def) => mlFun name def) ndefs

    -- mainCode <- mlExpr ctm
    
    -- support <- readDataFile "ocaml/support.ml"

    -- let generatedCode = concat funcs ++ mainFunc mainCode
    -- let code = support ++ generatedCode

    let code = "hiii"
    let out = outputDir </> outfile <.> "ml"
    Right () <- coreLift (writeFile out code)
        | Left err => throw (FileErr out err)
    pure (Just out)

||| OCaml implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm =
    throw $ InternalError "OCaml backend is only able to compile at the moment"

export
codegenOcaml : Codegen
codegenOcaml = MkCG compileExpr executeExpr

main : IO ()
main = mainWithCodegens [("ocaml", codegenOcaml)]
