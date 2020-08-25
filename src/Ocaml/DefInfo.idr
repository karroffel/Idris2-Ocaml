||| Extracting type information from function and constructor definitions.
|||
||| By matching all arrows in a function or constructor type all "primitive"
||| types are extracted as best as possible.
|||
||| Because type information is limited, this does not work well across type
||| aliases or functions, it's only a best effort.

module Ocaml.DefInfo

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Data.NameMap
import Data.Vect
import Data.List

||| Abstract types that are used to specialise items that
||| use "primitive" types.
|||
||| Any non-primitive type *or* type that can't be extracted
||| is represented as `SOpaque`
public export
data SType = SErased
           | SInt
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
    SErased == SErased = True
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
        SErased => "(erased)"
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

export
stypeFromConst : Constant -> SType
stypeFromConst IntType = SInt
stypeFromConst IntegerType = SInteger
stypeFromConst Bits8Type = SBits8
stypeFromConst Bits16Type = SBits16
stypeFromConst Bits32Type = SBits32
stypeFromConst Bits64Type = SBits64
stypeFromConst StringType = SString
stypeFromConst CharType = SChar
stypeFromConst DoubleType = SDouble
stypeFromConst WorldType = SWorld
stypeFromConst _ = SOpaque

fromTerm : Term names -> SType
fromTerm (PrimVal fc c) = stypeFromConst c
fromTerm _ = SOpaque

export
fromCFType : CFType -> SType
fromCFType CFUnit = SErased
fromCFType CFInt = SInt
fromCFType CFUnsigned8 = SBits8
fromCFType CFUnsigned16 = SBits16
fromCFType CFUnsigned32 = SBits32
fromCFType CFUnsigned64 = SBits64
fromCFType CFString = SString
fromCFType CFChar = SChar
fromCFType CFDouble = SDouble
fromCFType CFWorld = SWorld
fromCFType _ = SOpaque

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

||| Replace all types at `erase` indices with `SErased`
eraseTypes : (idx : Nat) -> (erase : List Nat) -> List SType -> List SType
eraseTypes n (i::is) (a::as) =
    if n == i
        then SErased :: eraseTypes (S n) is as
        else a :: eraseTypes (S n) (i::is) as
eraseTypes _ _ args = args

||| Remove all elements at `idxs` indices
removeIdxs : (idx : Nat) -> (idxs : List Nat) -> List a -> List a
removeIdxs n (i::is) (a::as) =
    if n == i
        then removeIdxs (S n) is as
        else a :: removeIdxs (S n) (i::is) as
removeIdxs _ _ args = args

||| Type information about a function or constructor
public export
record DefInfo where
    constructor MkDefInfo
    argTypes : List SType
    restType : SType
    
public export
DefInfos : Type
DefInfos = NameMap DefInfo

||| Extract type information of all the provided defs
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
                    -- For functions replace types of erased arguments with SErased
                    -- as not all function invocations will always go through `App`s
                    -- that have all type information. 
                    let res = extractTypes (length args) glob.type
                        restTy = res.restType
                        argTys = res.argTypes ++ replicate res.leftOverArgs SOpaque
                        argTys' = eraseTypes 0 glob.eraseArgs argTys
                        info = MkDefInfo argTys' restTy
                    in inner {c = c} (insert name info acc) defs
                MkNmCon tag arity nt => 
                    -- For constructors all erased arguments need to be removed
                    -- from the arg-types list. Constructor expressions will only
                    -- supply non-erased arguments and pattern matching will only
                    -- extract non-erased arguments, so removing them entirely
                    -- is the way to go here.
                    let res = extractTypes arity glob.type
                        restTy = res.restType
                        argTys = res.argTypes ++ replicate res.leftOverArgs SOpaque
                        argTys' = removeIdxs 0 glob.eraseArgs argTys
                        info = MkDefInfo argTys' restTy
                    in inner {c = c} (insert name info acc) defs

                MkNmForeign ccs argTys ret => do
                    let info = MkDefInfo (map fromCFType argTys) (fromCFType ret)
                    inner {c = c} (insert name info acc) defs
                MkNmError x => inner {c = c} acc defs