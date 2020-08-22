module Ocaml.Ocaml

import Idris.Driver

import Compiler.Common
import Compiler.CompileExpr

import Core.Context
import Core.Directory

import Utils.Path

import Data.List
import Data.NameMap
import Data.Maybe
import Data.Vect

import System
import System.File

import Ocaml.Expr
import Ocaml.DefInfo


mlDef : {auto di : DefInfos} ->
        Name ->
        NamedDef ->
        Core String
mlDef name (MkNmFun args expr) = do
    Just info <- pure $ lookup name di
        | Nothing => throw $ InternalError $ "No Extracted type for function " ++ show name
    
    let args' = info.argTypes `zip` args
        ret = info.restType

    let argDecls = showSep " " $ map (\(ty, n) => "(" ++ mlName n ++ " : " ++ ocamlTypeName ty ++ ")") args'
        header = "and " ++ mlName name ++ " " ++ argDecls ++ " : " ++ ocamlTypeName ret ++ " = "
    
    code <- mlExpr {funArgs = empty} expr
    pure $ header ++ code.source ++ "\n\n"
    
mlDef name (MkNmCon tag arity nt) = pure ""
mlDef name (MkNmForeign ccs fargs x) = pure ""
mlDef name (MkNmError msg) = pure ""

mainFunc : {auto di : DefInfos} -> NamedCExp -> Core String
mainFunc expr = do
    code <- mlExpr {funArgs = empty} expr
    pure $ "let main = " ++ code.source ++ ";;"


||| OCaml implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
    ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile = do
    cData <- getCompileData Cases tm
    let ndefs = namedDefs cData
    let ctm = forget (mainExpr cData)

    defs <- get Ctxt
    let context = gamma defs

    diMap <- buildDefInfoMap ndefs
    
    support <- readDataFile "ocaml/support.ml"

    defsCode <- traverse (\(name, _, def) => mlDef name def) ndefs

    mainCode <- mainFunc ctm
    let generatedCode = concat defsCode ++ mainCode
        code = support ++ generatedCode

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
