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

    and BoundInstE =
        { Constructor: Constructor
          ArgInsts: InstE list }

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
        | IsGround
        | GroundnessUnknown

    and InstContainsAny =
        | DoesNotContainAny
        | ContainsAny
        | ContainsAnyUnknown

    and InstContainsInstNames =
        | ContainsInstNames of HashSet<InstName>
        | ContainsInstNamesUnknown

    and InstTestResults =
        { Groundness: InstIsGround
          ContainsAny: InstContainsAny
          ContainsInstNames: InstContainsInstNames }
        static member noResults =
            { Groundness = GroundnessUnknown
              ContainsAny = ContainsAnyUnknown
              ContainsInstNames = ContainsInstNamesUnknown }

    type InstDet = InstE * Determinism

    let rec ofInst (inst: Inst) : InstE =
        match inst with
        | Inst.NotReached -> InstE.NotReached
        | Inst.Free -> InstE.Free
        | Inst.Ground -> InstE.Ground
        | Inst.Any -> InstE.Any
        | Inst.HigherOrder (mode) ->
            let modes =
                List.map (fun (inst1, inst2) -> (ofInst inst1, ofInst inst2)) mode.Modes

            InstE.HigherOrder (modes, mode.Determinism)
        | Inst.Bound (boundInsts) -> InstE.Bound (InstTestResults.noResults, List.map ofBoundInst boundInsts)

    and ofBoundInst (boundInst: BoundInst) : BoundInstE =
        { Constructor = boundInst.Constructor
          ArgInsts = (List.map ofInst boundInst.ArgInsts) }

    type InstTable() =
        member this.unifyInsts = Dictionary<InstPair, InstDet option> ()
        member this.mergeInsts = Dictionary<InstPair, InstE option> ()
        member this.groundInsts = Dictionary<InstName, InstDet option> ()
        member this.anyInsts = Dictionary<InstName, InstDet option> ()

        static member private lookupInst(table: Dictionary<'K, 'V>, inst: 'K) =
            match table.TryGetValue inst with
            | true, value -> value
            | false, _ -> raise (System.Exception ($"inst not found ${inst}"))

        static member private searchInsertInst(table: Dictionary<'K, 'V option>, inst: 'K) =
            match table.TryGetValue inst with
            | true, value -> Some value
            | false, _ ->
                do table.Add (inst, None)
                None

        static member private updateInst(table: Dictionary<'K, 'V>, inst: 'K, value: 'V) =
            do table.[inst] <- value
            ()

        member this.expand(inst) =
            match inst with
            | DefinedInst (name) -> this.lookup name |> this.expand
            | _ -> inst

        member this.lookup(instName: InstName) : InstE =
            let handleInstDet instName instDet : InstE =
                match instDet with
                | Some (inst, _) -> inst
                | None -> DefinedInst (instName)

            match instName with
            | UnifyInst (instPair) ->
                InstTable.lookupInst (this.unifyInsts, instPair)
                |> handleInstDet instName
            | MergeInst (instPair) ->
                let mergeInst =
                    InstTable.lookupInst (this.mergeInsts, instPair)

                match mergeInst with
                | Some (inst) -> inst
                | None -> DefinedInst (instName)
            | GroundInst (instName) ->
                InstTable.lookupInst (this.groundInsts, instName)
                |> handleInstDet instName
            | AnyInst (instName) ->
                InstTable.lookupInst (this.anyInsts, instName)
                |> handleInstDet instName

        member this.instContainsInstName(inst: InstE, instName: InstName) : bool = false

        member this.instIsBoundOrAny(inst: InstE) : bool = false

        member this.boundInstIsGroundOrAny(inst: BoundInstE) : bool = false

        member this.boundInstListIsGroundOrAny(instResults: InstTestResults, argInsts: BoundInstE list) : bool = false

        member this.makeGroundInst(inst: InstE) : (InstE * Determinism) option =
            match inst with
            | NotReached -> Some (NotReached, Erroneous)
            | Any -> Some (Ground, Semidet)
            | Free -> Some (Ground, Det)
            | Bound (results, boundInsts) ->
                this.makeGroundBoundInstList boundInsts
                |> Option.map (fun res -> (Bound (results, fst res), parallelConjunctionDeterminism Semidet (snd res)))
            | Ground -> Some (Ground, Semidet)
            | HigherOrder _ -> Some (inst, Semidet)
            | DefinedInst (instName) ->
                let groundInstName = GroundInst (instName)

                let maybeInstDet =
                    InstTable.searchInsertInst (this.groundInsts, instName)

                match maybeInstDet with
                | Some (Some (groundInst, det)) -> Some (groundInst, det)
                | Some (None) ->
                    // We can safely assume this is det, since if it were semidet,
                    // we would have noticed this in the process of unfolding the
                    // definition.
                    Some (DefinedInst (groundInstName), Determinism.Det)
                | None ->
                    let maybeGroundInstDet =
                        this.lookup (instName)
                        |> this.expand
                        |> this.makeGroundInst

                    do InstTable.updateInst (this.groundInsts, instName, maybeGroundInstDet)
                    // Avoid expanding recursive insts.
                    maybeGroundInstDet
                    |> Option.map
                        (fun groundInstDet ->
                            if (this.instContainsInstName (fst groundInstDet, groundInstName)) then
                                (DefinedInst (groundInstName), snd groundInstDet)
                            else
                                groundInstDet)

        member this.makeGroundInstList(insts: InstE list) : (InstE list * Determinism) option =
            let makeGroundInstFolder det inst =
                this.makeGroundInst inst
                |> Option.map (fun res -> (fst res, parallelConjunctionDeterminism det (snd res)))

            Util.mapFoldOption makeGroundInstFolder Det insts

        member this.makeGroundBoundInstList(insts: BoundInstE list) : (BoundInstE list * Determinism) option =
            let makeGroundBoundInst det boundInst =
                this.makeGroundInstList (boundInst.ArgInsts)
                |> Option.map
                    (fun res ->
                        ({ Constructor = boundInst.Constructor
                           ArgInsts = fst res },
                         parallelConjunctionDeterminism det (snd res)))

            Util.mapFoldOption makeGroundBoundInst Det insts

        member this.makeAnyInst(inst: InstE) : (InstE * Determinism) option =
            match inst with
            | NotReached -> Some (NotReached, Erroneous)
            | Any -> Some (Any, Semidet)
            | Free -> Some (Any, Det)
            | Bound (results, boundInsts) ->
                this.makeAnyBoundInstList boundInsts
                |> Option.map (fun res -> (Bound (results, fst res), parallelConjunctionDeterminism Semidet (snd res)))
            | Ground -> Some (Ground, Semidet)
            | HigherOrder _ -> Some (inst, Semidet)
            | DefinedInst (instName) ->
                let anyInstName = AnyInst (instName)

                let maybeInstDet =
                    InstTable.searchInsertInst (this.anyInsts, instName)

                match maybeInstDet with
                | Some (Some (anyInstDet)) -> Some (anyInstDet)
                | Some (None) ->
                    // We can safely assume this is det, since if it were semidet,
                    // we would have noticed this in the process of unfolding the
                    // definition.
                    Some (DefinedInst (anyInstName), Determinism.Det)
                | None ->
                    let maybeAnyInstDet =
                        this.lookup (instName)
                        |> this.expand
                        |> this.makeAnyInst

                    do InstTable.updateInst (this.anyInsts, instName, maybeAnyInstDet)
                    // Avoid expanding recursive insts.
                    maybeAnyInstDet
                    |> Option.map
                        (fun anyInstDet ->
                            if (this.instContainsInstName (fst anyInstDet, anyInstName)) then
                                (DefinedInst (anyInstName), snd anyInstDet)
                            else
                                anyInstDet)

        member this.makeAnyInstList(insts: InstE list) : (InstE list * Determinism) option =
            let makeAnyInstFolder det inst =
                this.makeAnyInst inst
                |> Option.map (fun res -> (fst res, parallelConjunctionDeterminism det (snd res)))

            mapFoldOption makeAnyInstFolder Det insts

        member this.makeAnyBoundInstList(insts: BoundInstE list) : (BoundInstE list * Determinism) option =
            let makeAnyBoundInst det boundInst =
                this.makeAnyInstList (boundInst.ArgInsts)
                |> Option.map
                    (fun res ->
                        ({ Constructor = boundInst.Constructor
                           ArgInsts = fst res },
                         parallelConjunctionDeterminism det (snd res)))

            mapFoldOption makeAnyBoundInst Det insts

        member this.unifyInstList(insts1: InstE list, insts2: InstE list) : (InstE list * Determinism) option = None

        member this.unifyInst(inst1: InstE, inst2: InstE) : InstDet option =
            let unifyInst3 inst1 inst2 =
                match inst1 with
                | NotReached -> Some (NotReached, Det)
                | Free ->
                    match inst2 with
                    | NotReached -> Some (NotReached, Det)
                    | Free -> None
                    | Bound (testResults, boundInsts) ->
                        // Disallow free-free unifications.
                        if (this.boundInstListIsGroundOrAny (testResults, boundInsts)) then
                            Some (inst2, Det)
                        else
                            None
                    | Ground
                    | HigherOrder (_)
                    | Any -> Some (inst2, Det)
                    | DefinedInst (_) -> None
                | Bound (testResults1, boundInsts1) ->
                    match inst2 with
                    | NotReached -> Some (NotReached, Det)
                    | Free ->
                        // Disallow free-free unifications.
                        if (this.boundInstListIsGroundOrAny (testResults1, boundInsts1)) then
                            Some (inst1, Det)
                        else
                            None
                    | Ground ->
                        match testResults1.Groundness with
                        | InstIsGround.IsGround -> Some (inst1, Semidet)
                        | InstIsGround.GroundnessUnknown
                        | InstIsGround.NotGround ->
                            match this.makeGroundBoundInstList (boundInsts1) with
                            | Some (boundInsts, det) ->
                                let testResults =
                                    { Groundness = InstIsGround.IsGround
                                      ContainsAny = InstContainsAny.DoesNotContainAny
                                      ContainsInstNames = InstContainsInstNames.ContainsInstNamesUnknown }

                                Some (Bound (testResults, boundInsts), det)
                            | None -> None
                    | Any ->
                        match this.makeAnyBoundInstList (boundInsts1) with
                        | Some (boundInsts, det) -> Some (Bound (InstTestResults.noResults, boundInsts), det)
                        | None -> None
                    | Bound (_, boundInsts2) ->
                        this.unifyBoundInstList (boundInsts1, boundInsts2)
                        |> Option.map (fun (boundInsts, det) -> (Bound (InstTestResults.noResults, boundInsts), det))

            let unifyInst2 inst1 inst2 =
                let inst1' = this.expand inst1
                let inst2' = this.expand inst2
                let instDet = unifyInst3 inst1' inst2'

                match instDet with
                | Some (_, det) ->
                    if (numSolutions det) = NoSolutions then
                        Some (NotReached, det)
                    else
                        instDet
                | None -> None

            if (inst1 = Free || inst2 = Free) then
                unifyInst2 inst1 inst2
            else
                let instPair = (inst1, inst2)
                let instName = UnifyInst (instPair)

                let maybeUnifyInst =
                    InstTable.searchInsertInst (this.unifyInsts, instPair)

                let instDet0 =
                    match maybeUnifyInst with
                    | Some (maybeInst) ->
                        match maybeInst with
                        | Some (instDet) -> Some (instDet)
                        | None -> Some (DefinedInst (instName), Determinism.Det)
                    | None ->
                        let result = unifyInst2 inst1 inst2

                        match result with
                        | Some (inst, det) ->
                            this.unifyInsts.[(inst1, inst2)] <- Some (inst, det)
                            Some (inst, det)
                        | None -> None

                match instDet0 with
                | Some (inst, det) ->
                    // Avoid expanding recursive insts.
                    if (this.instContainsInstName (inst, instName)) then
                        Some (DefinedInst (instName), det)
                    else
                        Some (inst, det)
                | None -> None

        member this.unifyBoundInstList
            (
                boundInsts1: BoundInstE list,
                boundInsts2: BoundInstE list
            ) : (BoundInstE list * Determinism) option =
            let rec unifyBoundInstList2 (boundInsts1: BoundInstE list) (boundInsts2: BoundInstE list) =
                match (boundInsts1, boundInsts2) with
                | ([], []) -> Some ([], Determinism.Erroneous)
                | ([], _ :: _)
                | (_ :: _, []) -> Some ([], Determinism.Fail)
                | (boundInst1 :: boundInsts1', boundInst2 :: boundInsts2') ->
                    if (boundInst1.Constructor = boundInst2.Constructor) then
                        this.unifyInstList (boundInst1.ArgInsts, boundInst2.ArgInsts)
                        |> Option.bind
                            (fun (argInsts, det1) ->
                                unifyBoundInstList2 boundInsts1' boundInsts2'
                                |> Option.bind
                                    (fun (boundInstsTail, det2) ->
                                        let det = switchDeterminism det1 det2

                                        if (numSolutions det1 = NumSolutions.NoSolutions) then
                                            Some (boundInstsTail, det)
                                        else
                                            let boundInst =
                                                { Constructor = boundInst1.Constructor
                                                  ArgInsts = argInsts }

                                            Some (boundInst :: boundInstsTail, det)))
                    else if (boundInst1.Constructor < boundInst2.Constructor) then
                        None
                    else
                        None

            if (boundInsts1 = [] || boundInsts2 = []) then
                Some ([], Determinism.Erroneous)
            else
                unifyBoundInstList2 boundInsts1 boundInsts2
