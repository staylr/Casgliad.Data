namespace Kanren.Data.Compiler

open Kanren.Data

[<AutoOpen>]
module Inst =
    type InstE =
    | Free
    | Ground
    | HigherOrder of RelationMode
    | Bound of BoundInstE list
    | DefinedInst of InstName
    | NotReached
    and BoundInstE = { Contructor: Constructor; ArgInsts: InstE list }
    and InstName =
        | UnifyInst of InstPair
        | MergeInst of InstPair
        | GroundInst of InstName
        | AnyInst of InstName
        | TypedGround of System.Type
        | TypedInst of InstType: System.Type * InstName: InstName
    and InstPair = InstE * InstE

    let ofInst (inst: Inst) : InstE =
        match inst with
        | Inst.Free -> InstE.Free
        | Inst.Ground -> InstE.Ground


    type InstDet = InstE * Determinism

