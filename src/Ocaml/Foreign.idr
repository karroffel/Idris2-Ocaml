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

import Ocaml.DefInfo

idrisSupport : String -> String
idrisSupport s = "OcamlRts.C.Lib_libidris2_support." ++ s

implNames : List (String, String)
implNames = [
    ("Data.Strings.fastConcat", "OcamlRts.Bytes.concat"),
    ("System.prim__getArgs", "OcamlRts.System.get_args"),
    ("Prelude.Types.fastPack", "OcamlRts.String.pack"),
    ("Data.Buffer.prim__newBuffer", idrisSupport "idris2_newBuffer"),
    ("Data.Buffer.prim__bufferSize", idrisSupport "idris2_getBufferSize"),
    ("Data.Buffer.prim__copyData", idrisSupport "idris2_copyBuffer"),
    ("Data.Buffer.prim__getByte", idrisSupport "idris2_getBufferByte"),
    ("Data.Buffer.prim__getDouble", idrisSupport "idris2_getBufferDouble"),
    ("Data.Buffer.prim__getInt", idrisSupport "idris2_getBufferInt"),
    ("Data.Buffer.prim__getString", idrisSupport "idris2_getBufferString"),
    
    ("Data.Buffer.prim__setByte",  idrisSupport "idris2_setBufferByte"),
    ("Data.Buffer.prim__setDouble", idrisSupport "idris2_setBufferDouble"),
    ("Data.Buffer.prim__setInt", idrisSupport "idris2_setBufferInt"),
    ("Data.Buffer.prim__setString", idrisSupport "idris2_setBufferString")

    
]

{-
Data.Buffer.prim__bufferSize : [Buffer] -> Int | ccs : ["scheme:blodwen-buffer-size", "node:lambda:b => BigInt(b.length)"]
Data.Buffer.prim__copyData : [Buffer, Int, Int, Buffer, Int, %World] -> IORes Unit | ccs : ["scheme:blodwen-buffer-copydata", "node:lambda:(b1,o1,length,b2,o2)=>b1.copy(b2,Number(o2), Number(o1), Number(o1+length))"]
Data.Buffer.prim__getByte : [Buffer, Int, %World] -> IORes Int | ccs : ["scheme:blodwen-buffer-getbyte", "node:lambda:(buf,offset)=>BigInt(buf.readUInt8(Number(offset)))"]
Data.Buffer.prim__getDouble : [Buffer, Int, %World] -> IORes Double | ccs : ["scheme:blodwen-buffer-getdouble", "node:lambda:(buf,offset)=>buf.readDoubleLE(Number(offset))"]
Data.Buffer.prim__getInt : [Buffer, Int, %World] -> IORes Int | ccs : ["scheme:blodwen-buffer-getint", "node:lambda:(buf,offset)=>BigInt(buf.readInt64(Number(offset)))"]
Data.Buffer.prim__getString : [Buffer, Int, Int, %World] -> IORes String | ccs : ["scheme:blodwen-buffer-getstring", "node:lambda:(buf,offset,len)=>buf.slice(Number(offset), Number(offset+len)).toString('utf-8')"]
Data.Buffer.prim__newBuffer : [Int, %World] -> IORes Buffer | ccs : ["scheme:blodwen-new-buffer", "node:lambda:s=>Buffer.alloc(Number(s))"]
Data.Buffer.prim__setByte : [Buffer, Int, Int, %World] -> IORes Unit | ccs : ["scheme:blodwen-buffer-setbyte", "node:lambda:(buf,offset,value)=>buf.writeUInt8(Number(value), Number(offset))"]
Data.Buffer.prim__setDouble : [Buffer, Int, Double, %World] -> IORes Unit | ccs : ["scheme:blodwen-buffer-setdouble", "node:lambda:(buf,offset,value)=>buf.writeDoubleLE(value, Number(offset))"]
Data.Buffer.prim__setInt : [Buffer, Int, Int, %World] -> IORes Unit | ccs : ["scheme:blodwen-buffer-setint", "node:lambda:(buf,offset,value)=>buf.writeInt64(Number(value), Number(offset))"]
Data.Buffer.prim__setString : [Buffer, Int, String, %World] -> IORes Unit | ccs : ["scheme:blodwen-buffer-setstring", "node:lambda:(buf,offset,value)=>buf.write(value, Number(offset),buf.length - Number(offset), 'utf-8')"]
System.Clock.prim__clockTimeGcCpu : [%World] -> IORes System.Clock.OSClock  | ccs : ["scheme:blodwen-clock-time-gccpu"]
System.Clock.prim__clockTimeGcReal : [%World] -> IORes System.Clock.OSClock  | ccs : ["scheme:blodwen-clock-time-gcreal"]
System.Clock.prim__clockTimeMonotonic : [%World] -> IORes System.Clock.OSClock  | ccs : ["scheme:blodwen-clock-time-monotonic"]
System.Clock.prim__clockTimeProcess : [%World] -> IORes System.Clock.OSClock  | ccs : ["scheme:blodwen-clock-time-process"]
System.Clock.prim__clockTimeThread : [%World] -> IORes System.Clock.OSClock  | ccs : ["scheme:blodwen-clock-time-thread"]
System.Clock.prim__clockTimeUtc : [%World] -> IORes System.Clock.OSClock  | ccs : ["scheme:blodwen-clock-time-utc"]
System.Clock.prim__osClockNanosecond : [System.Clock.OSClock , %World] -> IORes Bits_64 | ccs : ["scheme:blodwen-clock-nanosecond"]
System.Clock.prim__osClockSecond : [System.Clock.OSClock , %World] -> IORes Bits_64 | ccs : ["scheme:blodwen-clock-second"]
System.Clock.prim__osClockValid : [System.Clock.OSClock , %World] -> IORes Int | ccs : ["scheme:blodwen-is-time?"]
System.prim__getArgs : [%World] -> IORes Prelude.Types.List String | ccs : ["scheme:blodwen-args", "node:lambda:() => __prim_js2idris_array(process.argv.slice(1))"]


-}

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
