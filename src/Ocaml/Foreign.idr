||| Foreign function definitions
|||
||| These are hardcoded and matched against the name for now.
||| If this backend ever gets included in the compiler then all those
||| mappings can be added to the functions in `libs/` instead.
module Ocaml.Foreign

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Debug.Trace

import Data.NameMap
import Data.Vect
import Data.List
import Data.List1
import Data.Strings

idrisSupport : String -> String
idrisSupport s = "OcamlRts.C.Lib_libidris2_support." ++ s

systemFn : String -> String
systemFn s = "OcamlRts.System." ++ s

implNames : List (String, String)
implNames = [
    ("Data.Strings.fastConcat", "OcamlRts.Bytes.concat"),
    ("Prelude.Types.fastPack", "OcamlRts.String.pack"),
    
    ("Data.Buffer.prim__newBuffer", idrisSupport "idris2_newBuffer"),
    ("Data.Buffer.prim__bufferSize", idrisSupport "idris2_getBufferSize"),
    ("Data.Buffer.prim__copyData", idrisSupport "idris2_copyBuffer"),
    ("Data.Buffer.prim__getByte", idrisSupport "idris2_getBufferByte"),
    ("Data.Buffer.prim__getDouble", idrisSupport "idris2_getBufferDouble"),
    ("Data.Buffer.prim__getInt", idrisSupport "idris2_getBufferInt"),
    ("Data.Buffer.prim__getBits8", idrisSupport "idris2_getBufferBits8"),
    ("Data.Buffer.prim__getBits16", idrisSupport "idris2_getBufferBits16"),
    ("Data.Buffer.prim__getBits32", idrisSupport "idris2_getBufferBits32"),
    ("Data.Buffer.prim__getBits64", idrisSupport "idris2_getBufferBits64"),
    ("Data.Buffer.prim__getString", idrisSupport "idris2_getBufferString"),
    ("Data.Buffer.prim__setByte",  idrisSupport "idris2_setBufferByte"),
    ("Data.Buffer.prim__setDouble", idrisSupport "idris2_setBufferDouble"),
    ("Data.Buffer.prim__setInt", idrisSupport "idris2_setBufferInt"),
    ("Data.Buffer.prim__setBits8", idrisSupport "idris2_setBufferBits8"),
    ("Data.Buffer.prim__setBits16", idrisSupport "idris2_setBufferBits16"),
    ("Data.Buffer.prim__setBits32", idrisSupport "idris2_setBufferBits32"),
    ("Data.Buffer.prim__setBits64", idrisSupport "idris2_setBufferBits64"),
    ("Data.Buffer.prim__setString", idrisSupport "idris2_setBufferString"),
    
    ("System.Clock.prim__clockTimeGcCpu", systemFn "clocktime_gc_cpu"),
    ("System.Clock.prim__clockTimeGcReal", systemFn "clocktime_gc_real"),
    ("System.Clock.prim__clockTimeMonotonic", systemFn "clocktime_monotonic"),
    ("System.Clock.prim__clockTimeProcess", systemFn "clocktime_process"),
    ("System.Clock.prim__clockTimeThread", systemFn "clocktime_thread"),
    ("System.Clock.prim__clockTimeUtc", systemFn "clocktime_utc"),
    ("System.Clock.prim__osClockNanosecond", systemFn "os_clock_nanosecond"),
    ("System.Clock.prim__osClockSecond", systemFn "os_clock_second"),
    ("System.Clock.prim__osClockValid", systemFn "os_clock_valid"),
    
    ("System.prim__getArgs", systemFn "get_args")
]

ccLibFun : List String -> Maybe String
ccLibFun [] = Nothing
ccLibFun (cc :: ccs) =
  if substr 0 3 cc == "ML:"
    then Just (substr 3 (length cc) cc)
    else if substr 0 2 cc == "C:"
        then case split (== ',') (substr 2 (length cc) cc) of
          [fn, libn] => Just ("OcamlRts.C.Lib_" ++ rmSpaces libn ++ "." ++ fn)
          _ => ccLibFun ccs  -- something strange -> skip
        else ccLibFun ccs  -- search further
  where
    rmSpaces : String -> String
    rmSpaces = pack . filter (/= ' ') . unpack



export
foreignFun : Name -> List String -> List CFType -> CFType -> String
foreignFun name ccs args ret =
    case ccLibFun ccs of
    Just name => name
    Nothing => case lookup (show name) implNames of
        Just fn => fn
        Nothing =>
            let msg = "Unsupported foreign function " ++ show name ++ " : " ++ show args ++ " -> " ++ show ret ++ " | ccs : " ++ show ccs in
            let src = "raise (Idris2_Exception \"Unsupported foreign function " ++ show name ++ " : " ++ show args ++ " -> " ++ show ret ++ "\")"
            in trace msg src
