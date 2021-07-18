namespace Kanren.Data.Compiler

open System.Collections.Generic

open Kanren.Data

[<AutoOpen>]
module Inst =
    type InstE =
    | Free
    | Ground
    | Any
    | HigherOrder of (InstE * InstE) list * Determinism
    | Bound of TestResults: InstTestResults * BoundInsts: BoundInstE list
    | DefinedInst of InstName
    | NotReached
    and BoundInstE = { Constructor: Constructor; ArgInsts: InstE list }
    and InstName =
        | UnifyInst of InstPair
        | MergeInst of InstPair
        | GroundInst of InstName
        | AnyInst of InstName
        | TypedGround of System.Type
        | TypedInst of InstType: System.Type * InstName: InstName
    and InstPair = InstE * InstE
    and InstIsGround =
        | NotGround
        | Ground
        | GroundnessUnknown
    and InstContainsAny =
        | DoesNotContainAny
        | ContainsAny
        | ContainsAnyUnknown
    and InstContainsInstNames =
        | ContainsInstNames of HashSet<InstName>
        | ContainsInstNamesUnknown
    and InstTestResults =
        { Groundness: InstIsGround;
            ContainsAny: InstContainsAny;
            ContainsInstNames: InstContainsInstNames }
        with static member noResults =
                { Groundness = GroundnessUnknown;
                    ContainsAny = ContainsAnyUnknown;
                    ContainsInstNames = ContainsInstNamesUnknown }

    type InstDet = InstE * Determinism

    let rec ofInst (inst: Inst) : InstE =
        match inst with
        | Inst.Free -> InstE.Free
        | Inst.Ground -> InstE.Ground
        | Inst.Any -> InstE.Any
        | Inst.HigherOrder(mode) ->
            let modes = List.map (fun (inst1, inst2) -> (ofInst inst1, ofInst inst2)) mode.Modes
            InstE.HigherOrder(modes, mode.Determinism)
        | Inst.Bound(boundInsts) ->
            InstE.Bound(InstTestResults.noResults, List.map ofBoundInst boundInsts)
    and ofBoundInst (boundInst: BoundInst) : BoundInstE =
            { Constructor = boundInst.Constructor
              ArgInsts = (List.map ofInst boundInst.ArgInsts) }

    type InstTable() =
        member this.unifyInsts = Dictionary<InstPair, InstDet option>()
        member this.mergeInsts =  Dictionary<InstPair, InstE option>()
        member this.groundInsts = Dictionary<InstName, InstDet option>()
        member this.anyInsts = Dictionary<InstName, InstDet option>()

        static member private lookupInst(table: Dictionary<'K, 'V>, insts: 'K) =
            match table.TryGetValue insts with
            | true, value -> value
            | false, _ -> raise (System.Exception($"inst not found ${insts}"))

        static member private searchInsertInst(table: Dictionary<'K, 'V option>, insts) =
            match table.TryGetValue insts with
            | true, value -> Some value
            | false, _ ->
                do table.Add(insts, None)
                None

        member this.expand(inst) =
            match inst with
            | DefinedInst (name) ->
                this.lookup name |> this.expand
            | _ ->
                inst

        member this.lookup(instName: InstName) : InstE =
            let handleInstDet instName instDet : InstE =
                match instDet with
                | Some (inst, _) -> inst
                | None -> DefinedInst (instName)

            match instName with
            | UnifyInst (instPair) ->
                InstTable.lookupInst(this.unifyInsts, instPair)
                |> handleInstDet instName
            | MergeInst (instPair) ->
                let mergeInst = InstTable.lookupInst(this.mergeInsts, instPair)
                match mergeInst with
                | Some (inst) ->
                    inst
                | None ->
                    DefinedInst (instName)
            | GroundInst (instName) ->
                InstTable.lookupInst(this.groundInsts, instName)
                |> handleInstDet instName
            | AnyInst (instName) ->
                InstTable.lookupInst(this.anyInsts, instName)
                |> handleInstDet instName

        member this.instContainsInstName(inst: InstE, instName: InstName) : bool = false

        member this.instIsBoundOrAny(inst: InstE) : bool = false

        member this.boundInstIsGroundOrAny(inst: BoundInstE) : bool = false

        member this.boundInstListIsGroundOrAny(instResults: InstTestResults, argInsts: BoundInstE list) : bool = false

        member this.makeGroundInst(inst: InstE) : (InstE * Determinism) option = None

        member this.makeGroundInstList(insts: InstE list) : (InstE list * Determinism) option = None

        member this.makeGroundBoundInstList(insts: BoundInstE list) : (BoundInstE list * Determinism) option = None
//
//            let makeGroundBoundInst boundInst det =
//                match this.makeGroundInstList(boundInst.ArgInsts) with
//                | Some (argInsts, det1) ->
//                    Some ({ Constructor = boundInst.Constructor; ArgInsts = argInsts },
//                          parallelConjunctionDeterminism det det1)
//                | None ->
//                    None
//            List.mapFold makeGroundBoundInst Det insts


        member this.unifyInst(inst1: InstE, inst2: InstE) : InstDet option =
            let unifyInst3 inst1 inst2 =
                match inst1 with
                | NotReached ->
                    Some (NotReached, Det)
                | Free ->
                    match inst2 with
                    | NotReached ->
                        Some (NotReached, Det)
                    | Free ->
                        None
                    | Bound (testResults, boundInsts) ->
                        // Disallow free-free unifications.
                        if (this.boundInstListIsGroundOrAny(testResults, boundInsts)) then
                            Some (inst2, Det)
                        else
                            None
                    | InstE.Ground ->
                        Some (inst2, Det)
                    | InstE.HigherOrder (_) ->
                        Some (inst2, Det)
                    | InstE.Any ->
                        Some (inst2, Det)
                    | InstE.DefinedInst(_) ->
                        None
                | Bound(testResults1, boundInsts1) ->
                    match inst2 with
                    | NotReached ->
                        Some (NotReached, Det)
                    | Free ->
                        // Disallow free-free unifications.
                        if (this.boundInstListIsGroundOrAny(testResults1, boundInsts1)) then
                            Some (inst1, Det)
                        else
                            None
                    | InstE.Ground ->
                        match testResults1.Groundness with
                        | InstIsGround.Ground ->
                            Some (inst1, Semidet)
                        | InstIsGround.GroundnessUnknown
                        | InstIsGround.NotGround ->
                            match this.makeGroundBoundInstList(boundInsts1) with
                            | Some (boundInsts, det) ->
                                let testResults =
                                    { Groundness = InstIsGround.Ground
                                      ContainsAny = InstContainsAny.DoesNotContainAny
                                      ContainsInstNames = InstContainsInstNames.ContainsInstNamesUnknown }
                                Some (Bound(testResults, boundInsts), det)
                            | None ->
                                None
            let unifyInst2 inst1 inst2 =
                let inst1' = this.expand inst1
                let inst2' = this.expand inst2
                let instDet = unifyInst3 inst1' inst2'
                match instDet with
                | Some (inst, det) ->
                    if (numSolutions det) = NoSolutions then
                        Some (NotReached, det)
                    else
                        instDet
                | None ->
                    None

            if (inst1 = Free || inst2 = Free) then
                unifyInst2 inst1 inst2
            else
                let instPair = (inst1, inst2)
                let instName = UnifyInst(instPair)
                let maybeUnifyInst = InstTable.searchInsertInst(this.unifyInsts, instPair)
                let instDet0 =
                    match maybeUnifyInst with
                    | Some (maybeInst) ->
                        match maybeInst with
                        | Some (instDet) ->
                            Some (instDet)
                        | None ->
                            Some (DefinedInst(instName), Determinism.Det)
                    | None ->
                        let result = unifyInst2 inst1 inst2
                        match result with
                        | Some (inst, det) ->
                            this.unifyInsts.[(inst1, inst2)] <- Some (inst, det)
                            Some (inst, det)
                        | None ->
                            None

                match instDet0 with
                | Some (inst, det) ->
                    // Avoid expanding recursive insts.
                    if (this.instContainsInstName(inst, instName)) then
                        Some (DefinedInst(instName), det)
                    else
                        Some (inst, det)
                | None ->
                    None
