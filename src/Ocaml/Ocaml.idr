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


import Ocaml.SpecialiseTypes


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

printTypeInfo : Context -> Name -> NamedDef -> Core ()
printTypeInfo ctxt name (MkNmFun args y) = do

    Just glob <- lookupCtxtExact name ctxt
        | Nothing => throw $ InternalError ("Unable to get GlobalDefs of " ++ show name)

    let typeInfo = extractTypes (length args) glob.type

    coreLift $ putStrLn $ "Fun Name            " ++ show name
    coreLift $ putStrLn $ "  Num args          " ++ show (length args)
    coreLift $ putStrLn $ "  Arg types         " ++ show typeInfo.argTypes
    coreLift $ putStrLn $ "  Ret type          " ++ show typeInfo.restType
    coreLift $ putStrLn $ "  Args left         " ++ show typeInfo.leftOverArgs

    -- coreLift $ putStrLn $ "   Type              " ++ show (glob.type)
    coreLift $ putStrLn $ "     Erase args      " ++ show (glob.eraseArgs)
    coreLift $ putStrLn $ "     Safe erase args " ++ show (glob.safeErase)
    -- coreLift $ putStrLn $ "     Spec args       " ++ show (glob.specArgs)
    coreLift $ putStrLn $ "     Inferrable args " ++ show (glob.inferrable)
    coreLift $ putStrLn ""

    pure ()
    
printTypeInfo ctxt name (MkNmCon tag arity nt) = do
    Just glob <- lookupCtxtExact name ctxt
        | Nothing => throw $ InternalError ("Unable to get GlobalDefs of " ++ show name)

    let typeInfo = extractTypes arity glob.type

    coreLift $ putStrLn $ "Con Name            " ++ show name
    coreLift $ putStrLn $ "  Num args          " ++ show arity
    coreLift $ putStrLn $ "  Arg types         " ++ show typeInfo.argTypes
    coreLift $ putStrLn $ "  Ret type          " ++ show typeInfo.restType
    coreLift $ putStrLn $ "  Args left         " ++ show typeInfo.leftOverArgs

    coreLift $ putStrLn $ "     Erase args      " ++ show (glob.eraseArgs)
    coreLift $ putStrLn $ "     Safe erase args " ++ show (glob.safeErase)
    coreLift $ putStrLn $ "     Inferrable args " ++ show (glob.inferrable)
    coreLift $ putStrLn ""

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
    
    support <- readDataFile "ocaml/support.ml"

    let generatedCode = "print_string \"Hello, world\";;"
    -- let generatedCode = concat funcs ++ mainFunc mainCode
    let code = support ++ generatedCode

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
