module Ocaml.Modules

import Compiler.ANF
import Compiler.Common
import Compiler.CompileExpr

import Core.TT

import Data.List
import Data.Strings
import Data.StringMap
import Data.NameMap
import Data.SortedSet
import Data.Vect

import Ocaml.Utils

adjust : String -> (v -> v) -> StringMap v -> StringMap v
adjust k f m =
    case lookup k m of
        Nothing => m
        Just v => insert k (f v) m


splitByNamespace : List (Name, ANFDef) -> List (String, List (Name, ANFDef))
splitByNamespace = StringMap.toList . foldl addOne StringMap.empty
    where
        addOne : StringMap (List (Name, ANFDef)) ->
                 (Name, ANFDef) ->
                 StringMap (List (Name, ANFDef))
        addOne nss def@(n, nd) =
            StringMap.mergeWith
                (++)
                (StringMap.singleton (namespace' n) [def])
                nss







-- forward declaration
tarjan : StringMap (SortedSet String) -> List (List String)
findExpr : ANF -> SortedSet String

nsDef : ANFDef -> SortedSet String
nsDef (MkAFun argNs rhs) = findExpr rhs
nsDef (MkACon tag arity) = SortedSet.empty
nsDef (MkAForeign ccs fargs rty) = SortedSet.empty
nsDef (MkAError rhs) = findExpr rhs

||| Information about module splitting
|||
||| Generally one module = one namespace, but modules can contain inline
||| namespaces, in which case there are more namespaces than modules, creating
||| possibly mutually recursive namespaces.
|||
||| One namespace of the group will be "elected" to be the identifier for the
||| group.
public export
record ModulesInfo where
    constructor MkModulesInfo
    components : List (List String)
    namespaceMapping : StringMap String
    defsByNamespace : StringMap (List (Name, ANFDef))
    dependencies : StringMap (SortedSet String)

total
export
moduleGroupIdentifier : (l : List String) -> NonEmpty l => String
moduleGroupIdentifier (n::ns) = (foldl min n ns)

export
modules : List (Name, ANFDef) -> ModulesInfo
modules defs =
    let
        defsByNS = StringMap.fromList $ splitByNamespace defs
        defDepsRaw = [StringMap.singleton (namespace' n) (SortedSet.delete (namespace' n) (nsDef d)) | (n, d) <- defs]
        defDeps = foldl (StringMap.mergeWith SortedSet.union) StringMap.empty defDepsRaw
        components = reverse $ tarjan defDeps  -- tarjan generates reverse toposort
        nsMapping = foldl
            (\nm, modNames => case modNames of
                [] => nm
                mn::mns =>
                    let mlMod = moduleGroupIdentifier (mn::mns)
                    in foldl (\nm, modName => StringMap.insert modName mlMod nm)
                        nm
                        modNames
            )
            StringMap.empty
            components
    in MkModulesInfo components nsMapping defsByNS defDeps


public export
record Module where
    constructor MkModule
    name : String
    defs : List (Name, ANFDef)
    deps : SortedSet String

export
moduleDefs : ModulesInfo -> List Module
moduleDefs info = flip concatMap info.components $ \mnames => case mnames of
    [] => []
    n::ns =>
        let
            groupId = moduleGroupIdentifier (n::ns)
            defs = concatMap
                    (\mname =>
                        fromMaybe
                        [] 
                        (StringMap.lookup mname info.defsByNamespace)
                    )
                    mnames
            deps = foldl
                    (\acc,name =>
                        let currDeps = fromMaybe SortedSet.empty $ StringMap.lookup name info.dependencies
                            resolved = flip map (SortedSet.toList currDeps) $ \n => 
                                fromMaybe n $ StringMap.lookup n info.namespaceMapping
                        in SortedSet.union
                            (SortedSet.fromList resolved)
                            acc
                    )
                    SortedSet.empty
                    mnames
            deps' = SortedSet.delete groupId deps
        in [MkModule groupId defs deps']
        
    




-- https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm#The_algorithm_in_pseudocode
record TarjanVertex where
  constructor TV
  index : Int
  lowlink : Int
  inStack : Bool

record TarjanState where
  constructor TS
  vertices : StringMap TarjanVertex
  stack : List String
  nextIndex : Int
  components : List (List String)
  impossibleHappened : Bool

tarjan deps = loop initialState (StringMap.keys deps)
    where
        initialState : TarjanState
        initialState =
            TS
                StringMap.empty
                []
                0
                []
                False

        strongConnect : TarjanState -> String -> TarjanState
        strongConnect ts v =
            let ts'' = case StringMap.lookup v deps of
                          Nothing => ts'  -- no edges
                          Just edgeSet => loop ts' (SortedSet.toList edgeSet)
            in case StringMap.lookup v ts''.vertices of
                    Nothing => record { impossibleHappened = True } ts''
                    Just vtv =>
                        if vtv.index == vtv.lowlink
                          then createComponent ts'' v []
                          else ts''
        where
            createComponent : TarjanState -> String -> List String -> TarjanState
            createComponent ts v acc =
                case ts.stack of
                    [] => record { impossibleHappened = True } ts
                    w :: ws =>
                        let ts' = record {
                                    vertices $= adjust w record{ inStack = False },
                                    stack = ws
                                  } ts
                        in if w == v
                            then record { components $= ((v :: acc) ::) } ts'  -- that's it
                            else createComponent ts' v (w :: acc)

            loop : TarjanState -> List String -> TarjanState
            loop ts [] = ts
            loop ts (w :: ws) =
                loop (
                    case StringMap.lookup w ts.vertices of
                        Nothing => let ts' = strongConnect ts w in
                            case StringMap.lookup w ts'.vertices of
                                Nothing => record { impossibleHappened = True } ts'
                                Just wtv =>
                                    record {
                                        vertices $= adjust v record {
                                                lowlink $= min wtv.lowlink
                                            }
                                    } ts'

                        Just wtv => case wtv.inStack of
                                        False => ts  -- nothing to do
                                        True =>
                                            record {
                                                vertices $= adjust v record {
                                                        lowlink $= min wtv.index
                                                    }
                                                } ts
                ) ws

            ts' : TarjanState
            ts' = record {
                    vertices  $= StringMap.insert v (TV ts.nextIndex ts.nextIndex True),
                    stack     $= (v ::),
                    nextIndex $= (1+)
                }ts

        loop : TarjanState -> List String -> List (List String)
        loop ts [] =
            if ts.impossibleHappened
                then []
                else ts.components
        loop ts (v :: vs) =
            case StringMap.lookup v ts.vertices of
                Just _ => loop ts vs  -- done, skip
                Nothing => loop (strongConnect ts v) vs








-- find references to other namespaces

mutual
    findExpr (AV fc v) = SortedSet.empty
    findExpr (AAppName fc name args) = SortedSet.insert (namespace' name) SortedSet.empty
    findExpr (AUnderApp fc name missing args) = SortedSet.insert (namespace' name) SortedSet.empty
    findExpr (AApp fc base arg) = SortedSet.empty
    findExpr (ALet fc var rhs expr) = findExpr rhs <+> findExpr expr
    findExpr (ACon fc name tag args) = SortedSet.empty
    findExpr (AOp fc fn args) = SortedSet.empty
    findExpr (AExtPrim fc name args) = SortedSet.empty
    findExpr (AConCase fc _ alts def) = concatMap findConAlt alts <+> concatMap findExpr def
    findExpr (AConstCase fc _ alts def) = concatMap findConstAlt alts <+> concatMap findExpr def
    findExpr (APrimVal fc _) = SortedSet.empty
    findExpr (AErased fc) = SortedSet.empty
    findExpr (ACrash fc msg) = SortedSet.empty
    
    findConAlt : AConAlt -> SortedSet String
    findConAlt (MkAConAlt name tag args rhs) = findExpr rhs
    
    findConstAlt : AConstAlt -> SortedSet String
    findConstAlt (MkAConstAlt const rhs) = findExpr rhs
