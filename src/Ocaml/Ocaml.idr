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
import System.Directory
import System.File
import System.Info


import Ocaml.Expr
import Ocaml.DefInfo
import Ocaml.Foreign

findOcamlFind : IO String
findOcamlFind = pure "ocamlfind" -- TODO


mlDef : {auto di : DefInfos} ->
        Name ->
        NamedDef ->
        Core String
mlDef name (MkNmFun args expr) = do
    Just info <- pure $ lookup name di
        | Nothing => throw $ InternalError $ "No Extracted type for function " ++ show name
    
    let args' = args `zip` info.argTypes
        ret = info.restType

    
    let argDecls = showSep " " $ map (\(n, ty) => "(" ++ mlName n ++ " : " ++ ocamlTypeName ty ++ ")") args'
        argDecls' = if isNil args' then "()" else argDecls -- functions without arguments have weird limitations
        header = "and " ++ mlName name ++ " " ++ argDecls' ++ " : " ++ ocamlTypeName ret ++ " = "
    
    code <- castedExpr {funArgs = fromList args'} ret expr
    pure $ header ++ code.source ++ "\n\n"
    
mlDef name (MkNmCon tag arity nt) = pure ""
mlDef name (MkNmForeign ccs argTys retTy) = do
    let argTys' = map fromCFType argTys
        retTy' = fromCFType retTy
        argNames = map (("arg_" ++) . show) [1..(length argTys')]
        args = argNames `zip` argTys'
        argDecls = showSep " " $ map (\(name, ty) => "(" ++ name ++ " : " ++ ocamlTypeName ty ++ ")") args
        args' = if isNil args then "()" else argDecls
    let header = "and " ++ mlName name ++ " " ++ args' ++ " : " ++ ocamlTypeName retTy' ++ " = "
        callArgs = if isNil argTys' then ["()"] else argNames

    pure $ header ++ foreignFun name ++ " " ++ showSep " " callArgs ++ "\n\n"
mlDef name (MkNmError msg) = pure ""

mainFunc : {auto di : DefInfos} -> NamedCExp -> Core String
mainFunc expr = do
    code <- mlExpr {funArgs = empty} expr
    pure $ "and main () = " ++ code.source ++ ";;\n\nmain ();;"


||| OCaml implementation of the `compileExpr` interface.
compileExpr : (mkexec : Bool) -> Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
    ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr mkexec c tmpDir outputDir tm outfile = do
    let appDirRel = outfile ++ "_app" -- relative to build dir
    let appDirGen = outputDir </> appDirRel -- relative to here
    coreLift $ mkdirAll appDirGen
    Just cwd <- coreLift currentDir
        | Nothing => throw (InternalError "Can't get current directory")

    let ext = if isWindows then ".exe" else ""
    let outMlFile = appDirRel </> outfile <.> "ml"
    let outBinFile = appDirRel </> outfile <.> ext
    let outMlAbs = cwd </> outputDir </> outMlFile
    let outBinAbs = cwd </> outputDir </> outBinFile

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

    Right () <- coreLift (writeFile outMlAbs code)
        | Left err => throw (FileErr outMlAbs err)

    ok <- the (Core Int) $ if mkexec
        then do
            ocamlFind <- coreLift findOcamlFind
            coreLift . system $ ocamlFind ++ " ocamlopt -package zarith -linkpkg -w -26-8 " ++ outMlAbs ++ " -o " ++ outBinAbs
        else
            pure 0
    
    if ok == 0
        then if mkexec
            then pure (Just outBinAbs)
            else pure (Just outMlAbs)
        else pure Nothing

||| OCaml implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm = do
    Just bin <- compileExpr True c tmpDir tmpDir tm "tmpocaml"
        | Nothing => throw (InternalError "compileExpr returned Nothing")
    coreLift $ system bin
    pure ()
-- throw $ InternalError "OCaml backend is only able to compile at the moment"

export
codegenOcaml : Codegen
codegenOcaml = MkCG (compileExpr True) executeExpr

main : IO ()
main = mainWithCodegens [("ocaml", codegenOcaml)]
