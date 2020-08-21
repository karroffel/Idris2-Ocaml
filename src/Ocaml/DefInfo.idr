module Ocaml.DefInfo

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.NameMap
import Data.Vect
import Data.List

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
Eq SType where
    SInt == SInt = True
    SInteger == SInteger = True
    SBits8 == SBits8 = True
    SBits16 == SBits16 = True
    SBits32 == SBits32 = True
    SBits64 == SBits64 = True
    SString == SString = True
    SChar == SChar = True
    SDouble == SDouble = True
    SWorld == SWorld = True
    SOpaque == SOpaque = True
    _ == _ = False

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
binderInner (Lam fc x y z) = z
binderInner (Let fc x val y) = y
binderInner (Pi fc x y z) = z
binderInner (PVar fc x y z) = z
binderInner (PLet fc x val y) = y
binderInner (PVTy fc x y) = y


record ExtractionResult (ty : Type) where
    constructor MkExtRes
    argTypes : List ty
    restType : ty
    leftOverArgs : Nat

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

extractTypes : (numArgs : Nat) -> ClosedTerm -> ExtractionResult SType
extractTypes numArgs term =
    let res = extractRawTypes numArgs [] term
        argTypes = map (\(_ ** t) => fromTerm t) res.argTypes
        restType = fromTerm (snd res.restType)
    in MkExtRes argTypes restType res.leftOverArgs


public export
record DefInfo where
    constructor MkDefInfo
    eraseArgs : List Nat
    argTypes : List SType
    leftOverArgs : Nat
    restType : SType
    
public export
DefInfos : Type
DefInfos = NameMap DefInfo

export
buildDefInfoMap : {auto c : Context} -> List (Name, FC, NamedDef) -> Core DefInfos
buildDefInfoMap xs = inner empty xs
    where
        inner : {auto c : Context} ->
                DefInfos ->
                List (Name, FC, NamedDef) ->
                Core DefInfos
        inner acc [] = pure acc
        inner acc ((name, _, def)::defs) = do
            Just glob <- lookupCtxtExact name c
                | Nothing => throw $ InternalError ("Unable to get GlobalDefs of " ++ show name)

            case def of
                MkNmFun args _ => 
                    let res = extractTypes (length args) glob.type
                        restTy = res.restType
                        info = MkDefInfo glob.eraseArgs res.argTypes res.leftOverArgs restTy
                    in inner {c = c} (insert name info acc) defs
                MkNmCon tag arity nt => 
                    let res = extractTypes arity glob.type
                        restTy = res.restType
                        info = MkDefInfo glob.eraseArgs res.argTypes res.leftOverArgs restTy
                    in inner {c = c} (insert name info acc) defs

                -- skip for now
                MkNmForeign ccs fargs x => inner {c = c} acc defs
                MkNmError x => inner {c = c} acc defs



removeIdx : (start : Nat) -> List Nat -> List a -> List a
removeIdx n (i::idxs) (x::xs) =
    if i < n then
        removeIdx n idxs (x::xs)
    else if i == n then
        removeIdx (S n) idxs xs
    else
        x :: (removeIdx (S n) (i::idxs) xs)

removeIdx _ _ args = args




public export
record CallInfo where
    constructor MkCallInfo
    returnType : SType
    directArgs : List (SType, NamedCExp)
    restArgs : List NamedCExp

export
callInfo : DefInfo -> List NamedCExp -> CallInfo
callInfo di args =
    let
        numDArgs = length di.argTypes
        (dArgs, iArgs) = splitAt numDArgs args
        dArgs' = removeIdx 0 di.eraseArgs (zip di.argTypes dArgs)
        iArgs' = removeIdx numDArgs di.eraseArgs iArgs
    in MkCallInfo di.restType dArgs' iArgs'

export
defArgs : DefInfo -> List Name -> (List (SType, Name), SType)
defArgs di args =
    let tys = di.argTypes ++ replicate di.leftOverArgs SOpaque
        args' = removeIdx 0 di.eraseArgs (zip tys args)
    in (args', di.restType)