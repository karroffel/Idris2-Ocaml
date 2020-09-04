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
import Ocaml.OcamlCompiler


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
compileExpr : CompilerCommands c => (comp : c) ->
              Ref Ctxt Defs ->
              (tmpDir : String) ->
              (outputDir : String) ->
              ClosedTerm ->
              (outfile : String) ->
              Core (Maybe String)
compileExpr comp c tmpDir outputDir tm outfile = do
    let appDirRel = outfile ++ "_app" -- relative to build dir
    let appDirGen = outputDir </> appDirRel -- relative to here
    coreLift $ mkdirAll appDirGen
    Just cwd <- coreLift currentDir
        | Nothing => throw (InternalError "Can't get current directory")

    let ext = if isWindows then ".exe" else ""
    let outFile = cwd </> outputDir </> outfile <.> ext

    cData <- getCompileData Cases tm
    let ndefs = namedDefs cData
    let ctm = forget (mainExpr cData)

    ctxtDefs <- get Ctxt
    let context = gamma ctxtDefs
        modRelFileName = \ns,ext => appDirRel </> ns <.> ext
        modAbsFileName = \ns,ext => cwd </> outputDir </> modRelFileName ns ext

    diMap <- buildDefInfoMap ndefs

    let mods = modules ndefs

    modules <- for (moduleDefs mods) $ \mod => do
        
        let modName = mod.name
        let path = modAbsFileName modName "ml"
        
        Right mlFile <- coreLift $ openFile path WriteTruncate
            | Left err => throw (FileErr path err)
            
        let append = \strData => Core.Core.do
                Right () <- coreLift $ fPutStr mlFile strData
                    | Left err => throw (FileErr path err)
                coreLift $ fflush mlFile
    
        let imports = concatMap (++";;\n") $ map ("open "++) (SortedSet.toList mod.deps)
        
        append $ "open OcamlRts;;\n\n" ++
                imports ++ "\nlet rec "
        
        first <- coreLift $ newIORef True
        defsWritten <- coreLift $ newIORef (the Int 0)
        for_ mod.defs \(n,_,d) => do
            def <- mlDef n d
            if def == ""
                then pure ()
                else do
                    isFirst <- coreLift $ readIORef first
                    if isFirst
                        then coreLift $ writeIORef first False
                        else append "and "
                    append def
                    coreLift $ modifyIORef defsWritten (+1)
        
        append ";;"
        coreLift $ closeFile mlFile
        
        if !(coreLift $ readIORef defsWritten) == 0
            then do
                _ <- coreLift $ writeFile path ""
                pure ()
            else pure ()

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

    let cmdBuildRts = compileRTSCmd comp "OcamlRts"
        cmdBuildMods = concat $ [compileModuleCmd comp ns | ns <- modules]
                                ++ [compileModuleCmd comp "Main"]
        cmdLink = linkCmd comp
                    (modules ++ ["Main"])
                    ["ocaml_rts.o", "libidris2_support.a"]
                    "OcamlRts"
                    outFile
        
        cmdFull = cmdBuildRts ++ cmdBuildMods ++ cmdLink

    for_ cmdFull $ \cmd => do
        let cmd' = "cd " ++ appDirGen ++ " && " ++ cmd
        ok <- the (Core Int) . coreLift $ system cmd'
        log "codegen.ocaml.build" 2 $ "Running command `" ++ cmd ++ "`"
        if ok /= 0
            then throw . InternalError $ "Command `" ++ cmd ++ "` failed."
            else pure ()

    pure (Just outFile)

||| OCaml implementation of the `executeExpr` interface.
executeExpr : CompilerCommands c => (comp : c) ->
              Ref Ctxt Defs ->
              (tmpDir : String) ->
              ClosedTerm ->
              Core ()
executeExpr comp c tmpDir tm = do
    Just bin <- compileExpr comp c tmpDir tmpDir tm "tmpocaml"
        | Nothing => throw (InternalError "compileExpr returned Nothing")
    coreLift $ system bin
    pure ()

export
codegenOcaml : CompilerCommands c => (comp : c) -> Codegen
codegenOcaml comp = MkCG (compileExpr comp) (executeExpr comp)

main : IO ()
main =
    mainWithCodegens [
            ("ocaml-native", codegenOcaml $ nativeCompiler Nothing False),
            ("ocaml-native-debug", codegenOcaml $ nativeCompiler Nothing True),
            ("ocaml-bytecode", codegenOcaml $ bytecodeCompiler Nothing False),
            ("ocaml-bytecode-debug", codegenOcaml $ bytecodeCompiler Nothing True)
        ]
