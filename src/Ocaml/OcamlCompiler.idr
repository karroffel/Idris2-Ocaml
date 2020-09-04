module Ocaml.OcamlCompiler

import Utils.Path

import Data.List
import Data.Maybe
import Data.Strings


public export
interface CompilerCommands a where
    compileRTSCmd : a -> (name : String) -> List String
    compileModuleCmd : a -> (name : String) -> List String
    linkCmd : a -> (modules, nativeObjs : List String) -> (rtsName, output : String) -> List String

export
record NativeOptions where
    constructor MkNativeOptions
    flags : String
    command : String

export
nativeCompiler : (compilerCmd : Maybe String) -> (debug : Bool) -> NativeOptions
nativeCompiler compilerCmd debug =
    let f = if debug then "-g" else ""
        cmd = fromMaybe "ocamlfind ocamlopt" compilerCmd
    in MkNativeOptions f cmd


namespace Native

    public export
    implementation CompilerCommands NativeOptions where
        compileRTSCmd o name =
            let ml = name <.> "ml"
                mli = name <.> "mli"
                f = " -I +threads " ++ o.flags ++ " -package zarith"
            in [
                o.command ++ f ++ " -w -8 -i " ++ ml ++ " > " ++ mli,
                o.command ++ f ++ " -c " ++ mli,
                o.command ++ f ++ " -w -8 -c " ++ ml
            ]
        
        compileModuleCmd o name =
            [
                o.command ++ " -I +threads " ++ o.flags ++
                " -package zarith -c -w -20-24-26-8 " ++ (name <.> "ml")
            ]

        linkCmd o modules nativeObjs rtsName output = [unwords cmdParts]
            where
                cmdParts : List String
                cmdParts =
                    [
                        o.command ++ " -thread -package zarith -linkpkg -nodynlink " ++ o.flags,
                        unwords nativeObjs ++ " " ++ (rtsName <.> "cmx"),
                        "-w -20-24-26-8"
                    ] ++
                    [m <.> "cmx" | m <- modules] ++
                    ["-o " ++ output]
