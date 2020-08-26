module Ocaml.Ocaml

import Idris.Driver

import Compiler.Common
import Compiler.CompileExpr

import Core.Context
import Core.Directory

import Utils.Path

import Data.List
import Data.Strings
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
import Ocaml.Utils

findOcamlFind : IO String
findOcamlFind = pure "ocamlfind" -- TODO


||| Generate OCaml code for a "definition" (function, constructor, foreign func, etc)
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
        callArgs = filter (\(_, ty) => ty /= SWorld) args
    
        callArgs' = if isNil callArgs then ["(Obj.magic ())"] else map (\(n, _) => "(Obj.magic (" ++ n ++ "))") callArgs
        
        body = "(Obj.magic (" ++ foreignFun name ccs argTys retTy ++ " " ++ showSep " " callArgs' ++ "))"

    pure $ header ++ body ++ "\n\n"
    
mlDef name (MkNmError msg) = pure ""

||| Generate OCaml code for the main expression
mainFunc : {auto di : DefInfos} -> NamedCExp -> Core String
mainFunc expr = do
    code <- mlExpr {funArgs = empty} expr
    pure $ "and main () = " ++ code.source ++ ";;\n\nmain ();;"


||| OCaml implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
    ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tmpDir outputDir tm outfile = do
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

    Right mlFile <- coreLift $ openFile outMlAbs WriteTruncate
        | Left err => throw (FileErr outMlAbs err)
    
    let append = \strData => Core.Core.do
                    Right () <- coreLift $ fPutStr mlFile strData
                        | Left err => throw (FileErr outMlAbs err)
                    coreLift $ fflush mlFile

    append support

    for_ ndefs $ \(name, _, def) => do
        s <- mlDef name def
        append s
    
    append !(mainFunc ctm)

    coreLift $ closeFile mlFile

    let copy = \fn => Core.Core.do
        src <- readDataFile ("ocaml" </> fn)
        coreLift $ writeFile (appDirGen </> fn) src
    
    -- TMP HACK
    -- .a and .h files
    coreLift $ system $ unwords
        ["cp", "~/.idris2/idris2-0.2.1/lib/*", appDirGen]

    coreLift $ system $ "cp ~/.idris2/idris2-0.2.1/support/ocaml/ocaml_rts.o " ++ appDirGen
    coreLift $ system $ "cp ~/.idris2/idris2-0.2.1/support/ocaml/OcamlRts.ml " ++ appDirGen

    ok <- the (Core Int) $ do
            ocamlFind <- coreLift findOcamlFind
            let cmd = unwords [
                        "cd " ++ appDirGen,
                        "&& " ++ ocamlFind ++ " opt -I +threads -i OcamlRts.ml > OcamlRts.mli",
                        "&& " ++ ocamlFind ++ " opt -I +threads -c OcamlRts.mli",
                        "&& " ++ ocamlFind ++ " opt -I +threads -c OcamlRts.ml",
                        "&& " ++ ocamlFind ++ " opt -thread -package zarith -linkpkg -nodynlink"
                            ++ " ocaml_rts.o OcamlRts.cmx"
                            ++ " libidris2_support.a -w -20-24-26-8 "
                            ++ outMlAbs ++ " -o " ++ outBinAbs
                    ]
            coreLift . putStrLn $ "Running command: " ++ cmd
            coreLift . system $ cmd
    
    if ok == 0
        then pure (Just outBinAbs)
        else pure Nothing

||| OCaml implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm = do
    Just bin <- compileExpr c tmpDir tmpDir tm "tmpocaml"
        | Nothing => throw (InternalError "compileExpr returned Nothing")
    coreLift $ system bin
    pure ()
-- throw $ InternalError "OCaml backend is only able to compile at the moment"

export
codegenOcaml : Codegen
codegenOcaml = MkCG compileExpr executeExpr

main : IO ()
main = mainWithCodegens [("ocaml", codegenOcaml)]
