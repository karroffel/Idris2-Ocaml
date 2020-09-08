module Compiler.Typed

import Core.TT
import Core.Context

import Data.Vect
import Data.NameMap

public export
data TType : Type where
    TInt : TType
    TInteger : TType
    TBits8 : TType
    TBits16 : TType
    TBits32 : TType
    TBits64 : TType
    TDouble : TType
    TString : TType
    TChar : TType
    TWorld : TType
    TNamed : (1 name : Name) -> TType
    TTy : TType
    TFun : (1 inTy : TType) -> (1 outTy : TType) -> TType
    TDelayed : (1 _ : TType) -> TType
    TOpaque : TType
    
public export
record TDataConstructor where
    constructor MkTDataConstructor
    name : Name
    tag : Int
    argTys : List TType

public export
record TFuncSig where
    constructor MkTFuncSig
    name : Name
    argTys : List TType
    retTy : TType

public export
record TypedData where
    constructor MkTypedData
    types : NameMap (List TDataConstructor)
    constructors : NameMap (TDataConstructor, Name)
    functions : NameMap TFuncSig


public export
data TPrimFn : Vect n TType -> TType -> Type where
    TPAdd : (ty : TType) -> TPrimFn [ty, ty] ty
    TPSub : (ty : TType) -> TPrimFn [ty, ty] ty
    TPMul : (ty : TType) -> TPrimFn [ty, ty] ty
    TPDiv : (ty : TType) -> TPrimFn [ty, ty] ty
    TPMod : (ty : TType) -> TPrimFn [ty, ty] ty
    TPNeg : (ty : TType) -> TPrimFn [ty] ty
    TPShiftL : (ty : TType) -> TPrimFn [ty, ty] ty
    TPShiftR : (ty : TType) -> TPrimFn [ty, ty] ty
    TPBAnd : (ty : TType) -> TPrimFn [ty, ty] ty
    TPBOr : (ty : TType) -> TPrimFn [ty, ty] ty
    TPBXor : (ty : TType) -> TPrimFn [ty, ty] ty
    TPLT : (ty : TType) -> TPrimFn [ty, ty] ty
    TPLTE : (ty : TType) -> TPrimFn [ty, ty] ty
    TPEQ : (ty : TType) -> TPrimFn [ty, ty] ty
    TPGTE : (ty : TType) -> TPrimFn [ty, ty] ty
    TPGT : (ty : TType) -> TPrimFn [ty, ty] ty
    SPtrLength : TPrimFn [TString] TInt
    TPStrHead : TPrimFn [TString] TChar
    TPStrTail : TPrimFn [TString] TString
    TPStrIndex : TPrimFn [TString, TInt] TChar
    TPStrCons : TPrimFn [TChar, TString] TString
    TPStrAppend : TPrimFn [TString, TString] TString
    TPStrReverse : TPrimFn [TString] TString
    TPStrSubstr : TPrimFn [TInt, TInt, TString] TString -- offset, length, string
    TPDoubleExp : TPrimFn [TDouble] TDouble
    TPDoubleLog : TPrimFn [TDouble] TDouble
    TPDoubleSin : TPrimFn [TDouble] TDouble
    TPDoubleCos : TPrimFn [TDouble] TDouble
    TPDoubleTan : TPrimFn [TDouble] TDouble
    TPDoubleASin : TPrimFn [TDouble] TDouble
    TPDoubleACos : TPrimFn [TDouble] TDouble
    TPDoubleATan : TPrimFn [TDouble] TDouble
    TPDoubleSqrt : TPrimFn [TDouble] TDouble
    TPDoubleFloor : TPrimFn [TDouble] TDouble
    TPDoubleCeiling : TPrimFn [TDouble] TDouble
    TPCast : (from : TType) -> (to : TType) -> TPrimFn [from] to
    TPBelieveMe : (toTy : TType) -> TPrimFn [TTy, toTy, TOpaque] toTy
    TPCrash : (asTy : TType) -> TPrimFn [asTy, TString] asTy

    

mutual
    data TExpr : Type where
        TLocal : FC -> Name -> TExpr
        TLam : FC -> (arg : Name) -> (argTy : TType) -> (body : TExpr) -> TExpr
        TLet : FC -> (bindName : Name) -> (rhs : TExpr) -> (expr : TExpr) -> TExpr
        TAppName : FC -> (funcName : Name) -> (args : List TExpr) -> TExpr
        TApp : FC -> (base : TExpr) -> (args : List TExpr) -> TExpr
        TDataCon : FC -> (name : Name) -> (tag : Int) -> (args : List TExpr) -> TExpr
        TTypeCon : FC -> (name : Name) -> (args : List TExpr) -> TExpr
        TOp : FC -> TPrimFn argTys retTy -> Vect (Data.Vect.length argTys) TExpr -> TExpr
        TExtPrim : FC -> (name : Name) -> (args : List TExpr) -> TExpr
        TForce : FC -> TExpr -> TExpr
        TDelay : FC -> TExpr -> TExpr
        TDataConCase : FC -> TExpr -> List TDataConCaseAlt -> Maybe TExpr -> TExpr
        TTypeConCase : FC -> TExpr -> List TTypeConCaseAlt -> Maybe TExpr -> TExpr
        TConstCase : FC -> TExpr -> List TConstCaseAlt -> Maybe TExpr -> TExpr
        TPrimVal : FC -> Constant -> TExpr
        TErased : FC -> TExpr
        TCrash : FC -> (message : String) -> TExpr
        TCast : FC -> (expr : TExpr) -> (to : TType) -> TExpr

    data TDataConCaseAlt : Type where
        MkTDataConCaseAlt : (name : Name) -> (binds : List Name) -> (body : TExpr) -> TDataConCaseAlt
    
    data TTypeConCaseAlt : Type where
        MkTTypeConCaseAlt : (name : Name) -> (binds : List Name) -> (body : TExpr) -> TTypeConCaseAlt
    
    data TConstCaseAlt : Type where
        MkTConstCaseAlt : Constant -> (body : TExpr) -> TConstCaseAlt
