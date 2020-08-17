module Ocaml.SpecialiseTypes

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.Vect


public export
data SType = SInt
           | SInteger
           | SBits8
           | SBits16
           | SBits32
           | SBits64
           | SString
           | SChar
           | SDouble
           | SWorld
           | SOpaque

public export
Show SType where
    show s = case s of
        SInt => "Int"
        SInteger => "Integer"
        SBits8 => "Bits8"
        SBits16 => "Bits16"
        SBits32 => "Bits32"
        SBits64 => "Bits64"
        SString => "String"
        SChar => "Char"
        SDouble => "Double"
        SWorld => "World"
        SOpaque => "Opaque"

fromTerm : Term names -> SType
fromTerm (PrimVal fc IntType) = SInt
fromTerm (PrimVal fc IntegerType) = SInteger
fromTerm (PrimVal fc Bits8Type) = SBits8
fromTerm (PrimVal fc Bits16Type) = SBits16
fromTerm (PrimVal fc Bits32Type) = SBits32
fromTerm (PrimVal fc Bits64Type) = SBits64
fromTerm (PrimVal fc StringType) = SString
fromTerm (PrimVal fc CharType) = SChar
fromTerm (PrimVal fc DoubleType) = SDouble
fromTerm (PrimVal fc WorldType) = SWorld
fromTerm _ = SOpaque

binderInner : Binder ty -> ty
binderInner (Lam x y z) = z
binderInner (Let x val y) = y
binderInner (Pi x y z) = z
binderInner (PVar x y z) = z
binderInner (PLet x val y) = y
binderInner (PVTy x y) = y


public export
record ExtractionResult (ty : Type) where
    constructor MkExtRes
    argTypes : List ty
    restType : ty
    leftOverArgs : Nat

export
Show ty => Show (ExtractionResult ty) where
    show (MkExtRes argTypes restType leftOverArgs) =
        "{ args = " ++ show argTypes ++
            ", restType = " ++ show restType ++
            ", leftOverArgs = " ++ show leftOverArgs ++
            " }"


extractRawTypes : (numNames : Nat) ->
                  (names : List Name) ->
                  Term names ->
                  ExtractionResult (ns ** Term ns)
extractRawTypes 0     names x = MkExtRes [] (names ** x) 0
extractRawTypes (S k) names (Bind fc x b scope) =
    let inner = binderInner b
        res   = extractRawTypes k (x::names) scope
    in
    record { argTypes $= ((names ** inner)::) } res
extractRawTypes n     names x = MkExtRes [] (names ** x) n

export
extractTypes : (numArgs : Nat) -> ClosedTerm -> ExtractionResult SType
extractTypes numArgs term =
    let res = extractRawTypes numArgs [] term
        argTypes = map (\(_ ** t) => fromTerm t) res.argTypes
        restType = fromTerm (snd res.restType)
    in MkExtRes argTypes restType res.leftOverArgs