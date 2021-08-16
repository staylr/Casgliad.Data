namespace Kanren.Data.Compiler

open System.Collections.Generic
open FSharp.Reflection

open Kanren.Data

[<AutoOpen>]
module Inst =
    type InstE =
        | Free
        | Ground
        | Any
        | HigherOrder of RelationModeE
        | HigherOrderAny of RelationModeE
        | Bound of TestResults: InstTestResults * BoundInsts: BoundInstE list
        | DefinedInst of InstName
        | NotReached

    and ModeE = (InstE * InstE)

    and RelationModeE =
        { Modes: ModeE list
          Determinism: Determinism }

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

    type InstMatchInputs = { Inst1: InstE; Inst2: InstE; Type: System.Type option }

    let rec ofInst (inst: Inst) : InstE =
        match inst with
        | Inst.NotReached -> InstE.NotReached
        | Inst.Free -> InstE.Free
        | Inst.Ground -> InstE.Ground
        | Inst.Any -> InstE.Any
        | Inst.HigherOrder (mode) ->
            let modes =
                List.map (fun (inst1, inst2) -> (ofInst inst1, ofInst inst2)) mode.Modes

            InstE.HigherOrder { Modes = modes; Determinism = mode.Determinism }
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

        member private this.expandAndProcess
                                (f: HashSet<InstName> -> InstE -> 'A)
                                (expanded: HashSet<InstName>)
                                (instName: InstName)
                                (resultIfRecursive: 'A) =
            if (expanded.Add(instName)) then
                this.lookup (instName)
                |> f expanded
            else
                resultIfRecursive

        static member private maybeGetConsIdArgTypes(maybeType: System.Type option, ctor: Constructor) =
            match ctor with
            | Constant _ ->
                []
            | Tuple _ | Record _ | UnionCase _ ->
               match maybeType with
               | Some varType ->
                   constructorArgTypes ctor varType
                   |> List.map Some
               | None ->
                   [ 1 .. (constructorArity ctor) ]
                   |> Seq.map (fun _ -> None)
                   |> List.ofSeq

        static member private maybeGetHigherOrderArgTypes(maybeType: System.Type option, arity: int) =
            match maybeType with
            | Some relationType when relationType.IsInstanceOfType(typeof<Relation<_>>) ->
                let argTypes = relationType.GetGenericArguments()
                match argTypes with
                | [| argType |] ->
                    if (FSharpType.IsTuple(argType)) then
                        Type.constructorArgTypes (Type.tupleConstructor argType) argType
                        |> List.map Some
                    elif (FSharpType.IsRecord(argType)) then
                        Type.constructorArgTypes (Record argType) argType
                        |> List.map Some
                    else
                        [ Some argType ]
                | _ ->
                    failwith "Expected one type argument for Relation<_>"
            | _ ->
                [1 .. arity]
                |> Seq.map (fun _ -> None)
                |> List.ofSeq

        // A list(bound_inst) is ``complete'' for a given type iff it includes
        // each functor of the type and each argument of each functor is also
        // ``complete'' for its type.
        member this.boundInstListIsCompleteForType(expansions, (boundInsts: BoundInstE list), instType) =
            let ctors = allConstructorArgTypesForType instType
            if (ctors = []) then
                false
            else
                ctors
                |> List.forall
                        (fun (ctor, argTypes) ->
                            let matchingInst =
                                boundInsts
                                |> List.tryFind (fun boundInst -> boundInst.Constructor = ctor)
                            match matchingInst with
                            | Some matchedInst ->
                                List.forall2 (fun i t -> this.instIsCompleteForType(expansions, i, t)) matchedInst.ArgInsts argTypes
                            | None ->
                                false
                        )

        member this.instIsCompleteForType(expansions: HashSet<InstName>, inst: InstE, instType: System.Type) : bool =
            match inst with
            | DefinedInst instName ->
                if (expansions.Contains(instName)) then
                    true
                else
                    let inst' = this.lookup(instName)
                    let expansions' = HashSet<InstName>(expansions)
                    do expansions'.Add(instName) |> ignore
                    this.instIsCompleteForType(expansions', inst', instType)
            | Bound (_, boundInsts) ->
                this.boundInstListIsCompleteForType(expansions, boundInsts, instType)
            | Free | Any | Ground | HigherOrder _ | HigherOrderAny _ ->
                true
            | NotReached ->
                false

        member this.instContainsInstName(inst: InstE, instName: InstName) : bool =
            let rec instContainsInstName2 (expanded: HashSet<InstName>) inst =
                    match inst with
                    | Free | Ground | Any | NotReached | HigherOrder _ | HigherOrderAny _ ->
                        false
                    | Bound (testResults, boundInsts) ->
                        boundInstListContainsInstName expanded testResults boundInsts
                    | DefinedInst thisInstName ->
                        if (thisInstName = instName) then
                            true
                        elif (expanded.Add(instName)) then
                            let expandedInst = this.lookup (instName)
                            instContainsInstName2 expanded expandedInst
                        else
                            false

            and boundInstListContainsInstName expanded testResults boundInsts =
                boundInsts |>
                List.exists (fun boundInst -> List.exists (instContainsInstName2 expanded) boundInst.ArgInsts)

            instContainsInstName2 (HashSet<InstName>()) inst

        member this.instIsGroundOrAny(inst: InstE) : bool =
            let rec instIsGroundOrAny2 expanded inst =
                    match inst with
                    | Ground | Any | NotReached | HigherOrder _ | HigherOrderAny _ ->
                        true
                    | Bound (testResults, boundInsts) ->
                        this.boundInstListIsGroundOrAny (testResults, boundInsts)
                    | Free ->
                        false
                    | DefinedInst instName ->
                        this.expandAndProcess instIsGroundOrAny2 expanded instName true

            instIsGroundOrAny2 (HashSet<InstName>()) inst

        member this.boundInstListIsGroundOrAny(instResults: InstTestResults, boundInsts: BoundInstE list) : bool =
            boundInsts
            |> List.forall (fun b -> List.forall this.instIsGroundOrAny b.ArgInsts)

        member this.instIsGround(inst: InstE) : bool =
            let rec instIsGround2 expanded inst =
                    match inst with
                    | Ground | NotReached | HigherOrder _ ->
                        true
                    | Bound (testResults, boundInsts) ->
                        this.boundInstListIsGround (testResults, boundInsts)
                    | Free ->
                        false
                    | Any | HigherOrderAny _ ->
                        // TODO maybe_any_to_bound in inst_test.m
                        false
                    | DefinedInst instName ->
                        this.expandAndProcess instIsGround2 expanded instName true

            instIsGround2 (HashSet<InstName>()) inst

        member this.boundInstListIsGround(instResults: InstTestResults, boundInsts: BoundInstE list) : bool =
            boundInsts
            |> List.forall (fun b -> List.forall this.instIsGround b.ArgInsts)

        member this.makeGroundInst(inst: InstE) : (InstE * Determinism) option =
            match inst with
            | NotReached -> Some (NotReached, Erroneous)
            | Any -> Some (Ground, Semidet)
            | Free -> Some (Ground, Det)
            | Bound (results, boundInsts) ->
                this.makeGroundBoundInstList boundInsts
                |> Option.map (fun res -> (Bound (results, fst res), parallelConjunctionDeterminism Semidet (snd res)))
            | Ground -> Some (Ground, Semidet)
            | HigherOrder _ | HigherOrderAny _ -> Some (inst, Semidet)
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
            | HigherOrder _ | HigherOrderAny _ -> Some (inst, Semidet)
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

        member this.unifyInstList(insts1: InstE list, insts2: InstE list) : (InstE list * Determinism) option =
            let unifyInstPair det (inst1, inst2) =
                this.unifyInst (inst1, inst2)
                |> Option.map (fun res -> (fst res, parallelConjunctionDeterminism det (snd res)))

            List.zip insts1 insts2
            |> mapFoldOption unifyInstPair Det

        // Mode checking is like abstract interpretation. The predicates below
        // define the abstract unification operation which unifies two
        // instantiatednesses. If the unification would be illegal, then abstract
        // unification fails. If the unification would fail, then the abstract
        // unification will succeed, and the resulting instantiatedness will be
        // `not_reached'.
        // Compute the inst that results from abstractly unifying two variables.
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
                    | HigherOrder _
                    | HigherOrderAny _
                    | Any -> Some (inst2, Det)
                    | DefinedInst _ ->
                        None
                | Bound (testResults1, boundInsts1) ->
                    match inst2 with
                    | NotReached -> Some (NotReached, Det)
                    | Free ->
                        // Disallow free-free unifications.
                        if (this.boundInstListIsGroundOrAny (testResults1, boundInsts1)) then
                            Some (inst1, Det)
                        else
                            None
                    | HigherOrder _ | HigherOrderAny _ ->
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
                    | DefinedInst _ -> None
                | Ground ->
                    this.makeGroundInst (inst2)
                | HigherOrder _ | HigherOrderAny _ ->
                    match inst2 with
                    | NotReached -> Some (NotReached, Determinism.Det)
                    | Free -> Some (inst1, Determinism.Det)

                    /// Test unification of higher-order values not supported.
                    | Bound _
                    | Ground
                    | HigherOrder _
                    | HigherOrderAny _
                    | Any
                    | DefinedInst _ ->
                        None
                | Any ->
                    this.makeAnyInst (inst2)
                | DefinedInst _ ->
                    // Should have been expanded before we got here.
                    None

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
                        | None ->
                            do this.unifyInsts.Remove (instPair) |> ignore
                            None

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

            let resultSetMatchCanFail (res, det) = (res, switchDeterminism det Determinism.Fail)

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

                                        // If the unification of the two cons_ids is guaranteed
                                        // not to succeed, don't include it in the list.
                                        if (numSolutions det1 = NumSolutions.NoSolutions) then
                                            Some (boundInstsTail, det)
                                        else
                                            let boundInst =
                                                { Constructor = boundInst1.Constructor
                                                  ArgInsts = argInsts }

                                            Some (boundInst :: boundInstsTail, det)))
                    else if (boundInst1.Constructor < boundInst2.Constructor) then
                        unifyBoundInstList2 boundInsts1' boundInsts2
                        |> Option.map resultSetMatchCanFail
                    else
                        unifyBoundInstList2 boundInsts1 boundInsts2'
                        |> Option.map resultSetMatchCanFail

            if (boundInsts1 = [] || boundInsts2 = []) then
                Some ([], Determinism.Erroneous)
            else
                unifyBoundInstList2 boundInsts1 boundInsts2

        // Combine the insts found in different arms of a disjunction, switch, or
        // if-then-else. The information in InstC is the minimum of the information
        // in InstA and InstB. Where InstA and InstB specify a binding (free or
        // bound), it must be the same in both.
        member this.mergeInst(inst1: InstE, inst2: InstE, maybeType: System.Type option) : InstE option =
            // If they specify matching pred insts, but one is more precise
            // (specifies more info) than the other, then we want to choose
            // the least precise one.
            let mergeHigherOrderInfo ho1 ho2 = ho1 // TODO

            let instListMerge insts1 insts2 types =
                List.zip3 insts1 insts2 types
                |> mapOption this.mergeInst

            // The two input lists BoundInstsA and BoundInstsB must already be sorted.
            // Here we perform a sorted merge operation,
            // so that the functors of the output list BoundInsts are the union
            // of the functors of the input lists BoundInstsA and BoundInstsB.
            let rec boundInstListMerge
                        (boundInsts1: BoundInstE list)
                        (boundInsts2: BoundInstE list)
                        (maybeType: System.Type option) =
                match boundInsts1 with
                | [] ->
                    Some boundInsts2
                | boundInst1 :: boundInsts1' ->
                    match boundInsts2 with
                    | [] ->
                        Some boundInsts1
                    | boundInst2 :: boundInsts2' ->
                        if (boundInst1.Constructor = boundInst2.Constructor) then

                            let argTypes = InstTable.maybeGetConsIdArgTypes(maybeType, boundInst1.Constructor)
                            instListMerge boundInst1.ArgInsts boundInst2.ArgInsts argTypes
                            |> Option.bind
                                (fun argInsts ->
                                    boundInstListMerge boundInsts1' boundInsts2' maybeType
                                    |> Option.bind
                                        (fun tail ->
                                            let boundInst = { Constructor = boundInst1.Constructor; ArgInsts = argInsts }
                                            Some (boundInst :: tail)
                                        ))
                        elif (boundInst1.Constructor < boundInst2.Constructor) then
                            boundInstListMerge boundInsts1' boundInsts2 maybeType
                            |> Option.map (fun tail -> boundInst1 :: tail)
                        else
                            boundInstListMerge boundInsts1 boundInsts2' maybeType
                            |> Option.map (fun tail -> boundInst2 :: tail)

            let boundInstListMergeWithGround instResults1 boundInsts1 maybeType =
                if (this.boundInstListIsGround(instResults1, boundInsts1)) then
                    Some Ground
                elif (this.boundInstListIsGroundOrAny(instResults1, boundInsts1)) then
                    // TODO Can do better if we know the type.
                    Some Any
                else
                    None

            let rec mergeInst3 inst1 inst2 maybeType =
                match inst1, inst2 with
                | Any, Any ->
                    Some Any
                | Bound(testResults, boundInsts), Any
                | Any, Bound (testResults, boundInsts) ->
                    // TODO We will lose any higher-order info in boundInsts.
                    // We should at least check that there isn't any such info.
                    if (this.boundInstListIsGroundOrAny (testResults, boundInsts)) then
                        Some Any
                    else
                        None
                | Any, Ground
                | Ground, Any ->
                    Some Any
                | Ground, Ground ->
                    Some Ground
                | HigherOrder info1, HigherOrder info2 ->
                    Some (HigherOrder (mergeHigherOrderInfo info1 info2))
                | Bound (_, boundInsts1), Bound (_, boundInsts2) ->
                    boundInstListMerge boundInsts1 boundInsts2 maybeType
                    |> Option.map (fun boundInsts -> Bound (InstTestResults.noResults, boundInsts))
                | Bound (instResults, boundInsts), Ground
                | Ground, Bound (instResults, boundInsts) ->
                    boundInstListMergeWithGround instResults boundInsts maybeType
                | _ ->
                    None

            let rec mergeInst2 inst1 inst2 maybeType =
                let inst1' = this.expand(inst1)
                let inst2' = this.expand(inst2)
                if (inst2' = NotReached) then
                    Some inst1'
                else if (inst1' = NotReached) then
                    Some inst2'
                else
                    mergeInst3 inst1' inst2 maybeType

            match inst1, inst2 with
            | Bound _, Bound _ ->
                mergeInst2 inst1 inst2 maybeType
            | _ ->
                let instPair = (inst1, inst2)
                let instName = MergeInst (instPair)

                let maybeMergeInst =
                    InstTable.searchInsertInst (this.mergeInsts, instPair)

                let inst0 =
                    match maybeMergeInst with
                    | Some (maybeInst) ->
                        match maybeInst with
                        | Some (inst) -> Some (inst)
                        | None -> Some (DefinedInst (instName))
                    | None ->
                        let result = mergeInst2 inst1 inst2 maybeType

                        match result with
                        | Some inst ->
                            this.mergeInsts.[instPair] <- result
                            result
                        | None ->
                            do this.mergeInsts.Remove instPair |> ignore
                            None

                match inst0 with
                | Some (inst) ->
                    // Avoid expanding recursive insts.
                    if (this.instContainsInstName (inst, instName)) then
                        Some (DefinedInst (instName))
                    else
                        Some (inst)
                | None -> None

        member this.maybeAnyToBound (maybeType: System.Type option) : (InstE option) = None

        // inst_matches_final(InstA, InstB, ModuleInfo):
        //
        // Succeed iff InstA is compatible with InstB, i.e. iff InstA will satisfy
        // the final inst requirement InstB. This is true if the information
        // specified by InstA is at least as great as that specified by InstB,
        // and where the information is the same and both insts specify a binding,
        // the binding must be identical.
        member this.instMatchesFinal(inst1: InstE, inst2: InstE, maybeType: System.Type option) : bool =
            this.instMatchesInitial (inst2, inst1, maybeType)

        /// Succeed iff `InstA' specifies at least as much information as `InstB',
        /// and in those parts where they specify the same information, `InstA'
        /// is at least as instantiated as `InstB'. Thus, the call
        /// inst_matches_initial(not_reached, ground, _) succeeds, since
        /// not_reached contains more information than ground - but not vice versa.
        /// Similarly, inst_matches_initial(bound(a), bound(a;b), _) should
        /// succeed, but not vice versa.
        member this.instMatchesInitial(inst1: InstE, inst2: InstE, maybeType: System.Type option) : bool =
            let rec instMatchesInitial3 expanded inst1 inst2 maybeType =
                match inst1 with
                | Any ->
                    match inst2 with
                    | Any | Free ->
                        true
                    | NotReached | HigherOrder _ | HigherOrderAny _ | DefinedInst _ ->
                        false
                    | Ground | Bound _ ->
                        match this.maybeAnyToBound(maybeType) with
                        | Some inst1' ->
                            instMatchesInitial2 expanded inst1' inst2 maybeType
                        | None ->
                            false
                | Free ->
                    inst2 = Free
                | Bound (instResults1, boundInsts1) ->
                    match inst2 with
                    | Any | Free ->
                        true
                    | Bound (_, boundInsts2) ->
                        boundInstListMatchesInitial expanded boundInsts1 boundInsts2 maybeType
                    | Ground ->
                        this.boundInstListIsGround (instResults1, boundInsts1)
                    | DefinedInst _ | HigherOrder _ | HigherOrderAny _ | NotReached->
                        false
                | Ground ->
                    match inst2 with
                    | Ground | Any | Free ->
                        true
                    | Bound (_, boundInsts2) ->
                        match maybeType with
                        | Some instType ->
                            this.boundInstListIsCompleteForType((HashSet<InstName>()), boundInsts2, instType)
                                && groundMatchesInitialBoundInstList expanded boundInsts2 maybeType
                        | None ->
                            false
                    | DefinedInst _ | HigherOrder _ | HigherOrderAny _ | NotReached ->
                        false
                | HigherOrder info1 ->
                    match inst2 with
                    | HigherOrder info2 | HigherOrderAny info2 ->
                        higherOrderInstInfoMatches info1 info2 maybeType
                    | _ ->
                        false
                | HigherOrderAny info1->
                    match inst2 with
                    | HigherOrderAny info2 ->
                        higherOrderInstInfoMatches info1 info2 maybeType
                    | _ ->
                        false
                | NotReached ->
                    false
                | DefinedInst _ ->
                    false

            and instMatchesInitial2 (expanded: HashSet<InstMatchInputs>) inst1 inst2 maybeType =
                let input = { Inst1 = inst1; Inst2 = inst2; Type = maybeType }
                // TODO: HashSet isn't the right data structure. Want to use Set, but InstE is not comparable.
                if (expanded.Contains(input)) then
                    true
                else
                    let expanded' = HashSet<InstMatchInputs>(expanded)
                    do expanded'.Add(input) |> ignore
                    let inst1' = this.expand(inst1)
                    let inst2' = this.expand(inst2)
                    instMatchesInitial3 expanded' inst1' inst2' maybeType

            // Assumes that the check of `bound_inst_list_is_complete_for_type' is done by the caller.
            and groundMatchesInitialBoundInstList expanded boundInsts maybeType =
                boundInsts
                |> List.forall (fun boundInst ->
                                    let argTypes = InstTable.maybeGetConsIdArgTypes(maybeType, boundInst.Constructor)
                                    List.forall2 (instMatchesInitial2 expanded Ground)
                                            boundInst.ArgInsts argTypes
                               )

            // Here we check that the functors in the first list are a subset of the
            // functors in the second list. (If a bound(...) inst only specifies the
            // insts for some of the constructors of its type, then it implicitly means
            // that all other constructors must have all their arguments `not_reached'.)
            // The code here makes use of the fact that the bound_inst lists are sorted.
            and boundInstListMatchesInitial
                    (expanded: HashSet<InstMatchInputs>)
                    (boundInsts1: BoundInstE list)
                    (boundInsts2: BoundInstE list)
                    maybeType =
                match (boundInsts1, boundInsts2) with
                | ([], _) ->
                    true
                | (boundInst1 :: boundInsts1', boundInst2 :: boundInsts2') ->
                    if (boundInst1.Constructor = boundInst2.Constructor) then
                        let argTypes = InstTable.maybeGetConsIdArgTypes(maybeType, boundInst1.Constructor)
                        forall3 (instMatchesInitial2 expanded) boundInst1.ArgInsts boundInst2.ArgInsts argTypes
                    elif (boundInst1.Constructor > boundInst2.Constructor) then
                        boundInstListMatchesInitial expanded boundInsts1 boundInsts2' maybeType
                    else
                        false
                | _ ->
                    false

            and higherOrderInstInfoMatches (hoInst1: RelationModeE) (hoInst2: RelationModeE) maybeType : bool =
                let higherOrderArgModeMatches (mode1: ModeE) (mode2: ModeE) (maybeType: System.Type option) =
                    this.instMatchesFinal(fst mode2, fst mode1, maybeType)
                        && this.instMatchesFinal(snd mode1, snd mode2, maybeType)

                hoInst1.Determinism = hoInst2.Determinism
                &&
                    let argTypes = InstTable.maybeGetHigherOrderArgTypes (maybeType, hoInst1.Modes.Length)
                    forall3 higherOrderArgModeMatches hoInst1.Modes hoInst2.Modes argTypes

            instMatchesInitial2 (HashSet<InstMatchInputs>()) inst1 inst2 maybeType
