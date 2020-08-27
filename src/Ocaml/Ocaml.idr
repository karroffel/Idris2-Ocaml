module Ocaml.Ocaml

import Idris.Driver

import Compiler.Common
import Compiler.CompileExpr

import Core.Context
import Core.Directory

import Utils.Path

import Data.List
import Data.Strings
import Data.StringMap
import Data.SortedSet
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
import Ocaml.Modules

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
        header = mlName name ++ " " ++ argDecls' ++ " : " ++ ocamlTypeName ret ++ " = "
    
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
    let header = mlName name ++ " " ++ args' ++ " : " ++ ocamlTypeName retTy' ++ " = "
        callArgs = filter (\(_, ty) => ty /= SWorld) args
    
        callArgs' = if isNil callArgs then ["(Obj.magic ())"] else map (\(n, _) => "(Obj.magic (" ++ n ++ "))") callArgs
        
        body = "(Obj.magic (" ++ foreignFun name ccs argTys retTy ++ " " ++ showSep " " callArgs' ++ "))"

    pure $ header ++ body ++ "\n\n"
    
mlDef name (MkNmError msg) = do
    let header = mlName name ++ " () : idr2_opaque = "
    body <- castedExpr {funArgs = NameMap.empty} SOpaque msg
    pure $ header ++ body.source ++ "\n\n"

||| Generate OCaml code for the main expression
mainModule : {auto di : DefInfos} -> (deps : List String) -> NamedCExp -> Core String
mainModule deps expr = do
    code <- mlExpr {funArgs = NameMap.empty} expr
    
    let imports = "open OcamlRts;;\n\n" ++ (concatMap (\s => "open " ++ s ++ ";;\n") deps)
        body = code.source ++ ";;"

    pure $ imports ++ body



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
    let outBinFile = appDirRel </> outfile <.> ext
    let outBinAbs = cwd </> outputDir </> outBinFile

    cData <- getCompileData Cases tm
    let ndefs = namedDefs cData
    let ctm = forget (mainExpr cData)

    ctxtDefs <- get Ctxt
    let context = gamma ctxtDefs
        modRelFileName = \ns,ext => appDirRel </> ns <.> ext
        modAbsFileName = \ns,ext => cwd </> outputDir </> modRelFileName ns ext

    diMap <- buildDefInfoMap ndefs
    
    support <- readDataFile "ocaml/support.ml"

    let mods = modules ndefs
    coreLift $ printLn mods.components
    coreLift $ printLn mods.namespaceMapping
    
    modules <- for (moduleDefs mods) $ \mod => do
        let imports = concatMap (++";;\n") $ map ("open "++) (SortedSet.toList mod.deps)
        defs' <- traverse (\(n,_,d) => mlDef n d) mod.defs
        let defs'' = filter (/= "") defs'
        let modName = mod.name
            src = "open OcamlRts;;\n\n" ++
                imports ++
                "\nlet rec " ++ showSep "and " defs''
                ++ ";;"
        
        let src' = if isNil defs''
                    then ""
                    else src
        
        let path = modAbsFileName modName "ml"
        Right () <- coreLift $ writeFile path src'
            | Left err => throw $ FileErr path err
        
        pure modName
    
    let mainImports =
            let raw = StringMap.keys mods.defsByNamespace
                resolved = SortedSet.fromList . flip map raw $ \n =>
                    fromMaybe n $ StringMap.lookup n mods.namespaceMapping
            in SortedSet.toList resolved
    
    mainMod <- mainModule mainImports ctm
    let mainPathML = cwd </> outputDir </> appDirRel </> "Main.ml"
    let mainPathCMX = cwd </> outputDir </> appDirRel </> "Main.cmx"
    
    Right () <- coreLift $ writeFile mainPathML mainMod
            | Left err => throw $ FileErr mainPathML err
    
    
    -- TMP HACK
    -- .a and .h files
    coreLift $ system $ unwords
        ["cp", "~/.idris2/idris2-0.2.1/lib/*", appDirGen]

    coreLift $ system $ "cp ~/.idris2/idris2-0.2.1/support/ocaml/ocaml_rts.o " ++ appDirGen
    coreLift $ system $ "cp ~/.idris2/idris2-0.2.1/support/ocaml/OcamlRts.ml " ++ appDirGen
    
    
    let cmdBuildModules = ["ocamlfind opt -I +threads -package zarith -c -w -20-24-26-8 " ++ modAbsFileName ns "ml" | ns <- modules]
                            ++ ["ocamlfind opt -I +threads -package zarith -c -w -20-24-26-8 " ++ mainPathML]
        cmdLink = unwords $ [
                                "ocamlfind opt -thread -package zarith -linkpkg -nodynlink",
                                "ocaml_rts.o OcamlRts.cmx libidris2_support.a",
                                "-w -20-24-26-8"
                            ] ++
                            [modAbsFileName ns "cmx" | ns <- modules] ++
                            [mainPathCMX] ++
                            ["-o " ++ outBinAbs]
        cmdFullBuild = [
                "ocamlfind opt -I +threads -package zarith -w -8 -i OcamlRts.ml > OcamlRts.mli",
                "ocamlfind opt -I +threads -package zarith -c OcamlRts.mli",
                "ocamlfind opt -I +threads -package zarith -w -8 -c OcamlRts.ml"
            ] ++ cmdBuildModules ++ [cmdLink]
    
    for_ cmdFullBuild $ \cmd => do
        let cmd' = "cd " ++ appDirGen ++ " && " ++ cmd
        ok <- the (Core Int) . coreLift $ system cmd'
        if ok /= 0
            then throw . InternalError $ "Command `" ++ cmd ++ "` failed."
            else pure ()
    
    pure (Just outBinAbs)

||| OCaml implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
executeExpr c tmpDir tm = do
    Just bin <- compileExpr c tmpDir tmpDir tm "tmpocaml"
        | Nothing => throw (InternalError "compileExpr returned Nothing")
    coreLift $ system bin
    pure ()

export
codegenOcaml : Codegen
codegenOcaml = MkCG compileExpr executeExpr

main : IO ()
main = mainWithCodegens [("ocaml", codegenOcaml)]
