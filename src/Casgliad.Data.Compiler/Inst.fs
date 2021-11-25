namespace Casgliad.Data.Compiler

open System.Collections.Generic
open FSharp.Reflection

open Casgliad.Data

[<AutoOpen>]
module internal Inst =
    // Similar to Mercury insts, except unique and partially instantiated
    // insts are not supported.
    type BoundInstE =
        | Ground
        | Any
        | HigherOrder of RelationModeE
        | HigherOrderAny of RelationModeE
        | BoundCtor of BoundCtorDetailsE
        | DefinedInst of InstName: InstName
        | NotReached

    and [<Struct>] InstE =
        | Free
        | Bound of BoundInstE

    and ModeE = (InstE * BoundInstE)

    and RelationModeE =
        { Modes: ModeE list
          Determinism: Determinism }

    and [<CustomEquality; NoComparison>] BoundCtorDetailsE =
        { BoundInsts: BoundCtorInstE list
          TestResults: InstTestResults }
        override this.Equals(other: obj) =
            match other with
            | :? BoundCtorDetailsE as otherInst -> otherInst.BoundInsts = this.BoundInsts
            | _ -> false

        override this.GetHashCode() = this.BoundInsts.GetHashCode ()

    and BoundCtorInstE =
        { Constructor: Constructor
          ArgInsts: BoundInstE list }

    and InstName =
        | UnifyInst of InstPair
        | MergeInst of InstPair
        | GroundInst of InstName
        | AnyInst of InstName
        | TypedGround of System.Type
        | TypedInst of InstType: System.Type * InstName: InstName

    and InstPair = BoundInstE * BoundInstE

    and InstIsGround =
        | IsGround
        | ContainsAny
        | GroundnessUnknown

    and InstContainsInstNames =
        | ContainsInstNames of HashSet<InstName>
        | ContainsInstNamesUnknown

    and [<CustomEquality; NoComparison>] InstTestResults =
        { Groundness: InstIsGround
          ContainsInstNames: InstContainsInstNames }
        static member noResults =
            { Groundness = GroundnessUnknown
              ContainsInstNames = ContainsInstNamesUnknown }

        static member groundTestResults =
            { Groundness = IsGround
              ContainsInstNames = ContainsInstNames (HashSet<InstName> ()) }

        // TODO: avoiding testing the set for equality should be further up the hierarchy.
        override this.Equals(other: obj) =
            match other with
            | :? InstTestResults as otherResults -> otherResults.Groundness = this.Groundness
            | _ -> false

        override this.GetHashCode() = this.Groundness.GetHashCode ()

    type InstDet = BoundInstE * Determinism

    type InstMatchInputs =
        { Inst1: BoundInstE
          Inst2: BoundInstE
          Type: System.Type option }

    let initialFinalInstsIsOutput inst1 inst2 =
        match (inst1, inst2) with
        | (Free, Bound _) -> true
        | _ -> false

    type InstTable() =
        member this.unifyInsts = Dictionary<InstPair, InstDet option> ()

        member this.mergeInsts =
            Dictionary<InstPair, BoundInstE option> ()

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

        member this.expand(inst: BoundInstE) : BoundInstE =
            match inst with
            | DefinedInst name -> this.lookup name |> this.expand
            | _ -> inst

        member this.expand(inst: InstE) : InstE =
            match inst with
            | Free -> Free
            | Bound inst -> this.expand (inst) |> Bound

        member this.lookup(instName: InstName) : BoundInstE =
            let handleInstDet instName instDet : BoundInstE =
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
                | Some inst -> inst
                | None -> DefinedInst (instName)
            | GroundInst (instName) ->
                InstTable.lookupInst (this.groundInsts, instName)
                |> handleInstDet instName
            | AnyInst (instName) ->
                InstTable.lookupInst (this.anyInsts, instName)
                |> handleInstDet instName

        member private this.expandAndProcess
            (f: HashSet<InstName> -> BoundInstE -> 'A)
            (expanded: HashSet<InstName>)
            (instName: InstName)
            (resultIfRecursive: 'A)
            =
            if (expanded.Add (instName)) then
                this.lookup (instName) |> f expanded
            else
                resultIfRecursive

        static member maybeGetConsIdArgTypes(maybeType: System.Type option, ctor: Constructor) =
            match ctor with
            | Constant _ -> []
            | Tuple _
            | Record _
            | UnionCase _ ->
                match maybeType with
                | Some varType -> constructorArgTypes ctor varType |> List.map Some
                | None ->
                    [ 1 .. (constructorArity ctor) ]
                    |> Seq.map (fun _ -> None)
                    |> List.ofSeq

        static member maybeGetHigherOrderArgTypes(maybeType: System.Type option, arity: int) =
            match maybeType with
            | Some relationType when relationType.IsInstanceOfType (typeof<Relation<_>>) ->
                let argTypes = relationType.GetGenericArguments ()

                match argTypes with
                | [| argType |] ->
                    if (FSharpType.IsTuple (argType)) then
                        Type.constructorArgTypes (Type.tupleConstructor argType) argType
                        |> List.map Some
                    elif (FSharpType.IsRecord (argType)) then
                        Type.constructorArgTypes (Record argType) argType
                        |> List.map Some
                    else
                        [ Some argType ]
                | _ -> failwith "Expected one type argument for Relation<_>"
            | _ ->
                [ 1 .. arity ]
                |> Seq.map (fun _ -> None)
                |> List.ofSeq

        // A list(bound_inst) is ``complete'' for a given type iff it includes
        // each functor of the type and each argument of each functor is also
        // ``complete'' for its type.
        member this.boundInstListIsCompleteForType(expansions, (boundInsts: BoundCtorInstE list), instType) =
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
                            List.forall2
                                (fun i t -> this.instIsCompleteForType (expansions, i, t))
                                matchedInst.ArgInsts
                                argTypes
                        | None -> false)

        member this.instIsCompleteForType
            (
                expansions: HashSet<InstName>,
                inst: BoundInstE,
                instType: System.Type
            ) : bool =
            match inst with
            | DefinedInst (instName) ->
                if (expansions.Contains (instName)) then
                    true
                else
                    let inst' = this.lookup (instName)
                    let expansions' = HashSet<InstName> (expansions)
                    do expansions'.Add (instName) |> ignore
                    this.instIsCompleteForType (expansions', inst', instType)
            | BoundCtor (boundInsts) ->
                this.boundInstListIsCompleteForType (expansions, boundInsts.BoundInsts, instType)
            | Any
            | Ground
            | HigherOrder _
            | HigherOrderAny _ -> true
            | NotReached -> false

        member this.boundInstListContainedInstNames
            (
                expansions: HashSet<InstName>,
                instNames: HashSet<InstName>,
                boundInsts: BoundCtorDetailsE
            ) : unit =
            match boundInsts.TestResults.ContainsInstNames with
            | ContainsInstNames set ->
                set
                |> Seq.iter (fun i -> instNames.Add i |> ignore)
            | ContainsInstNamesUnknown ->
                boundInsts.BoundInsts
                |> List.iter
                    (fun b ->
                        b.ArgInsts
                        |> List.iter (fun i -> this.containedInstNames (expansions, instNames, i)))

        member this.containedInstNames
            (
                expansions: HashSet<InstName>,
                instNames: HashSet<InstName>,
                inst: BoundInstE
            ) : unit =
            match inst with
            | Ground
            | Any
            | NotReached
            | HigherOrder _
            | HigherOrderAny _ -> ()
            | BoundCtor (boundInsts) -> this.boundInstListContainedInstNames (expansions, instNames, boundInsts)
            | DefinedInst instName ->
                if (expansions.Add (instName)) then
                    let expandedInst = this.lookup (instName)
                    this.containedInstNames (expansions, instNames, expandedInst)
                else
                    ()

        member this.instContainsInstName(inst: BoundInstE, instName: InstName) : bool =
            let rec instContainsInstName2 (expanded: HashSet<InstName>) inst =
                match inst with
                | Ground
                | Any
                | NotReached
                | HigherOrder _
                | HigherOrderAny _ -> false
                | BoundCtor (boundInsts) ->
                    boundInstListContainsInstName expanded boundInsts.TestResults boundInsts.BoundInsts
                | DefinedInst thisInstName ->
                    if (thisInstName = instName) then
                        true
                    elif (expanded.Add (instName)) then
                        let expandedInst = this.lookup (instName)
                        instContainsInstName2 expanded expandedInst
                    else
                        false

            and boundInstListContainsInstName expanded testResults boundInsts =
                boundInsts
                |> List.exists (fun boundInst -> List.exists (instContainsInstName2 expanded) boundInst.ArgInsts)

            instContainsInstName2 (HashSet<InstName> ()) inst

        member this.testInstIsGround testResults f =
            match testResults.Groundness with
            | GroundnessUnknown -> f ()
            | IsGround -> true
            | ContainsAny -> false

        // TODO
        member this.instContainsAny(inst: InstE) : bool = false

        member this.instIsGround(inst: BoundInstE) : bool =
            let rec instIsGround2 expanded inst =
                match inst with
                | Ground
                | NotReached
                | HigherOrder _ -> true
                | BoundCtor (boundInsts) -> this.boundInstListIsGround (boundInsts)
                | Any
                | HigherOrderAny _ ->
                    // TODO maybe_any_to_bound in inst_test.m
                    false
                | DefinedInst instName -> this.expandAndProcess instIsGround2 expanded instName true

            instIsGround2 (HashSet<InstName> ()) inst

        member this.boundInstListIsGround(boundInsts: BoundCtorDetailsE) : bool =
            this.testInstIsGround
                boundInsts.TestResults
                (fun () ->
                    boundInsts.BoundInsts
                    |> List.forall (fun b -> List.forall this.instIsGround b.ArgInsts))

        member this.makeGroundInst(inst: BoundInstE) : (BoundInstE * Determinism) option =
            match inst with
            | NotReached -> Some (NotReached, Erroneous)
            | Any -> Some (Ground, Semidet)
            | BoundCtor (boundInsts) ->
                this.makeGroundBoundInstList boundInsts.BoundInsts
                |> Option.map
                    (fun res -> (this.makeBoundInst (fst res), parallelConjunctionDeterminism Semidet (snd res)))
            | Ground -> Some (Ground, Semidet)
            | HigherOrder _
            | HigherOrderAny _ -> Some (inst, Semidet)
            | DefinedInst instName ->
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

        member this.makeGroundInstList(insts: BoundInstE list) : (BoundInstE list * Determinism) option =
            let makeGroundInstFolder det inst =
                this.makeGroundInst inst
                |> Option.map (fun res -> (fst res, parallelConjunctionDeterminism det (snd res)))

            Util.mapFoldOption makeGroundInstFolder Det insts

        member this.makeGroundBoundInstList(insts: BoundCtorInstE list) : (BoundCtorInstE list * Determinism) option =
            let makeGroundBoundInst det boundInst =
                this.makeGroundInstList (boundInst.ArgInsts)
                |> Option.map
                    (fun res ->
                        ({ Constructor = boundInst.Constructor
                           ArgInsts = fst res },
                         parallelConjunctionDeterminism det (snd res)))

            Util.mapFoldOption makeGroundBoundInst Det insts

        member this.makeAnyInst(inst: BoundInstE) : (BoundInstE * Determinism) option =
            match inst with
            | NotReached -> Some (NotReached, Erroneous)
            | Any -> Some (Any, Semidet)
            | BoundCtor (boundInsts) ->
                this.makeAnyBoundInstList boundInsts.BoundInsts
                |> Option.map
                    (fun res -> (this.makeBoundInst (fst res), parallelConjunctionDeterminism Semidet (snd res)))
            | Ground -> Some (Ground, Semidet)
            | HigherOrder _
            | HigherOrderAny _ -> Some (inst, Semidet)
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

        member this.makeAnyInstList(insts: BoundInstE list) : (BoundInstE list * Determinism) option =
            let makeAnyInstFolder det inst =
                this.makeAnyInst inst
                |> Option.map (fun res -> (fst res, parallelConjunctionDeterminism det (snd res)))

            mapFoldOption makeAnyInstFolder Det insts

        member this.makeAnyBoundInstList(insts: BoundCtorInstE list) : (BoundCtorInstE list * Determinism) option =
            let makeAnyBoundInst det boundInst =
                this.makeAnyInstList (boundInst.ArgInsts)
                |> Option.map
                    (fun res ->
                        ({ Constructor = boundInst.Constructor
                           ArgInsts = fst res },
                         parallelConjunctionDeterminism det (snd res)))

            mapFoldOption makeAnyBoundInst Det insts

        member this.unifyInstList
            (
                insts1: BoundInstE list,
                insts2: BoundInstE list
            ) : (BoundInstE list * Determinism) option =
            let unifyInstPair det (inst1, inst2) =
                this.unifyBoundInst (inst1, inst2)
                |> Option.map (fun res -> (fst res, parallelConjunctionDeterminism det (snd res)))

            List.zip insts1 insts2
            |> mapFoldOption unifyInstPair Det

        member this.unifyBoundInst(inst1: BoundInstE, inst2: BoundInstE) : InstDet option =
            let unifyInst3 inst1 inst2 =
                match inst1 with
                | NotReached -> Some (NotReached, Det)
                | BoundCtor (boundInsts1) ->
                    match inst2 with
                    | NotReached -> Some (NotReached, Det)
                    | HigherOrder _
                    | HigherOrderAny _ -> None
                    | Ground ->
                        match boundInsts1.TestResults.Groundness with
                        | InstIsGround.IsGround -> Some (inst1, Semidet)
                        | InstIsGround.GroundnessUnknown
                        | InstIsGround.ContainsAny ->
                            match this.makeGroundBoundInstList (boundInsts1.BoundInsts) with
                            | Some (boundInsts, det) ->
                                let testResults =
                                    { Groundness = InstIsGround.IsGround
                                      ContainsInstNames = InstContainsInstNames.ContainsInstNamesUnknown }

                                Some (this.makeBoundInst (boundInsts), det)
                            | None -> None
                    | Any ->
                        match this.makeAnyBoundInstList (boundInsts1.BoundInsts) with
                        | Some (boundInsts, det) -> Some (this.makeBoundInst (boundInsts), det)
                        | None -> None
                    | BoundCtor (boundInsts2) ->
                        this.unifyBoundInstList (boundInsts1.BoundInsts, boundInsts2.BoundInsts)
                        |> Option.map (fun (boundInsts, det) -> (this.makeBoundInst (boundInsts), det))
                    | DefinedInst _ -> None
                | Ground -> this.makeGroundInst (inst2)
                | HigherOrder _
                | HigherOrderAny _ ->
                    match inst2 with
                    | NotReached -> Some (NotReached, Determinism.Det)

                    /// Test unification of higher-order values not supported.
                    | BoundCtor _
                    | Ground
                    | HigherOrder _
                    | HigherOrderAny _
                    | Any
                    | DefinedInst _ -> None
                | Any -> this.makeAnyInst (inst2)
                | DefinedInst _ ->
                    // Should have been expanded before we got here.
                    None

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

        // Mode checking is like abstract interpretation. The predicates below
        // define the abstract unification operation which unifies two
        // insts. If the unification would be illegal, then abstract
        // unification fails. If the unification would fail, then the abstract
        // unification will succeed, and the resulting instantiatedness will be
        // `not_reached'.
        // Compute the inst that results from abstractly unifying two variables.
        member this.unifyInst(inst1: InstE, inst2: InstE) : InstDet option =
            match (inst1, inst2) with
            | (Free, Bound boundInst2) -> Some (boundInst2, Det)
            | (Bound boundInst1, Free) -> Some (boundInst1, Det)
            | (Free, Free) -> None
            | (Bound boundInst1, Bound boundInst2) ->
                let instPair = (boundInst1, boundInst2)
                let instName = UnifyInst (instPair)

                let maybeUnifyInst =
                    InstTable.searchInsertInst (this.unifyInsts, instPair)

                let instDet0 =
                    match maybeUnifyInst with
                    | Some (maybeInst) ->
                        match maybeInst with
                        | Some (instDet) -> Some (instDet)
                        | None -> Some (DefinedInst instName, Determinism.Det)
                    | None ->
                        let result =
                            this.unifyBoundInst (boundInst1, boundInst2)

                        match result with
                        | Some (inst, det) ->
                            this.unifyInsts.[instPair] <- Some (inst, det)
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
                boundInsts1: BoundCtorInstE list,
                boundInsts2: BoundCtorInstE list
            ) : (BoundCtorInstE list * Determinism) option =

            let resultSetMatchCanFail (res, det) =
                (res, switchDeterminism det Determinism.Fail)

            let rec unifyBoundInstList2 (boundInsts1: BoundCtorInstE list) (boundInsts2: BoundCtorInstE list) =
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

        // Get the argument insts of unifying the given inst with the constructor.
        // The unification must succeed, or an exception will be thrown.
        member this.getArgInsts(inst: InstE, ctor: Constructor, arity: int) =
            match inst with
            | Free
            | Bound NotReached
            | Bound Ground
            | Bound Any -> List.replicate arity inst
            | Bound (BoundCtor details) ->
                match details.BoundInsts
                      |> List.tryFind (fun b -> b.Constructor = ctor) with
                | Some boundInst -> boundInst.ArgInsts |> List.map Bound
                | None -> failwith "InstTable.getArgInsts: could not find bound inst"
            | _ -> failwith $"InstTable.getARgInsts: unexpected inst {inst}"

        member this.unifyInstFunctor
            (
                inst: InstE,
                ctor: Constructor,
                argInsts: InstE list,
                varType: System.Type
            ) : InstDet option =

            let argBoundInsts =
                if (List.forall (fun i -> i <> Free) argInsts) then
                    Some (
                        List.map
                            (function
                            | Bound i -> i)
                            argInsts
                    )
                else
                    None

            match inst with
            | Bound NotReached -> Some (NotReached, Erroneous)
            | Free ->
                match argBoundInsts with
                | Some boundInsts -> Some (this.makeBoundInst (ctor, boundInsts), Det)
                | None ->
                    // Don't allow partially instantiated terms.
                    None
            | Bound Any ->
                // We only allow `any' to unify with a functor if we know that
                // the type is not a solver type.
                if (typeIsSolverType varType) then
                    None
                else
                    argInsts
                    |> Util.foldOption
                        (fun (insts, det) i ->
                            match i with
                            | Free -> Some (Any :: insts, det)
                            | Bound bi ->
                                this.makeAnyInst (bi)
                                |> Option.map
                                    (fun (anyInst, det1) -> (anyInst :: insts, parallelConjunctionDeterminism det det1)))
                        ([], Det)
                    |> Option.map (fun (insts, det) -> (this.makeBoundInst (ctor, List.rev insts), det))

            | Bound (BoundCtor boundInstList1) ->
                match List.tryFind (fun i -> i.Constructor = ctor) boundInstList1.BoundInsts with
                | Some (boundInst1) ->
                    Util.foldOption2
                        (fun (insts, det) i1 i2 ->
                            match i1 with
                            | Free -> Some (i2 :: insts, det)
                            | Bound _ ->
                                this.unifyInst (i1, Bound i2)
                                |> Option.map
                                    (fun (unifyInst, det1) ->
                                        (unifyInst :: insts, parallelConjunctionDeterminism det det1)))
                        ([], Det)
                        argInsts
                        boundInst1.ArgInsts
                    |> Option.map (fun (insts, det) -> (this.makeBoundInst (ctor, List.rev insts), det))
                | None -> None
            | Bound Ground ->
                argInsts
                |> Util.foldOption
                    (fun (insts, det) i ->
                        match i with
                        | Free -> Some (Ground :: insts, det)
                        | Bound bi ->
                            this.makeGroundInst (bi)
                            |> Option.map
                                (fun (groundInst, det1) ->
                                    (groundInst :: insts, parallelConjunctionDeterminism det det1)))
                    ([], Det)
                |> Option.map (fun (insts, det) -> (this.makeBoundInst (ctor, List.rev insts), det))
            | _ -> None

        // Combine the insts found in different arms of a disjunction, switch, or
        // if-then-else. The information in InstC ifs the minimum of the information
        // in InstA and InstB. Where InstA and InstB specify a binding (free or
        // bound), it must be the same in both.
        member this.mergeInst(inst1: InstE, inst2: InstE, maybeType: System.Type option) : InstE option =
            // If they specify matching pred insts, but one is more precise
            // (specifies more info) than the other, then we want to choose
            // the least precise one.
            let mergeHigherOrderInfo ho1 ho2 = ho1 // TODO

            let rec mergeInstList insts1 insts2 types =
                List.zip3 insts1 insts2 types
                |> mapOption mergeInst1

            // The two input lists BoundInstsA and BoundInstsB must already be sorted.
            // Here we perform a sorted merge operation,
            // so that the functors of the output list BoundInsts are the union
            // of the functors of the input lists BoundInstsA and BoundInstsB.
            and mergeBoundCtorInstList
                (boundInsts1: BoundCtorInstE list)
                (boundInsts2: BoundCtorInstE list)
                (maybeType: System.Type option)
                =
                match boundInsts1 with
                | [] -> Some boundInsts2
                | boundInst1 :: boundInsts1' ->
                    match boundInsts2 with
                    | [] -> Some boundInsts1
                    | boundInst2 :: boundInsts2' ->
                        if (boundInst1.Constructor = boundInst2.Constructor) then

                            let argTypes =
                                InstTable.maybeGetConsIdArgTypes (maybeType, boundInst1.Constructor)

                            mergeInstList boundInst1.ArgInsts boundInst2.ArgInsts argTypes
                            |> Option.bind
                                (fun argInsts ->
                                    mergeBoundCtorInstList boundInsts1' boundInsts2' maybeType
                                    |> Option.bind
                                        (fun tail ->
                                            let boundInst =
                                                { Constructor = boundInst1.Constructor
                                                  ArgInsts = argInsts }

                                            Some (boundInst :: tail)))
                        elif (boundInst1.Constructor < boundInst2.Constructor) then
                            mergeBoundCtorInstList boundInsts1' boundInsts2 maybeType
                            |> Option.map (fun tail -> boundInst1 :: tail)
                        else
                            mergeBoundCtorInstList boundInsts1 boundInsts2' maybeType
                            |> Option.map (fun tail -> boundInst2 :: tail)

            and mergeBoundInstListWithGround boundInsts1 maybeType =
                if (this.boundInstListIsGround (boundInsts1)) then
                    Some Ground
                else
                    // TODO Can do better if we know the type.
                    Some Any

            and mergeInst3 inst1 inst2 maybeType =
                match inst1, inst2 with
                | Any, Any -> Some Any
                | BoundCtor (boundInsts), Any
                | Any, BoundCtor (boundInsts) ->
                    // TODO We will lose any higher-order info in boundInsts.
                    // We should at least check that there isn't any such info.
                    Some Any
                | Any, Ground
                | Ground, Any -> Some Any
                | Ground, Ground -> Some Ground
                | HigherOrder info1, HigherOrder info2 -> Some (HigherOrder (mergeHigherOrderInfo info1 info2))
                | BoundCtor (boundInsts1), BoundCtor (boundInsts2) ->
                    mergeBoundCtorInstList boundInsts1.BoundInsts boundInsts2.BoundInsts maybeType
                    |> Option.map (fun boundInsts -> this.makeBoundInst (boundInsts))
                | BoundCtor (boundInsts), Ground
                | Ground, BoundCtor (boundInsts) -> mergeBoundInstListWithGround boundInsts maybeType
                | _ -> None

            and mergeInst2 (inst1: BoundInstE) (inst2: BoundInstE) maybeType =
                let inst1' = this.expand (inst1)
                let inst2' = this.expand (inst2)

                if (inst2' = NotReached) then
                    Some inst1'
                else if (inst1' = NotReached) then
                    Some inst2'
                else
                    mergeInst3 inst1' inst2 maybeType

            and mergeInst1 (inst1, inst2, maybeType) : BoundInstE option =
                // In cases where both InstA and InstB are bound/3, the merge_inst_table
                // does not work as a cache: actually doing merging the insts is likely
                // to be faster (and maybe *much* faster) than looking them up
                // in the merge_inst_table. And in such cases, the table is not needed
                // for termination either. Since the skeleton of the bound_inst list
                // does not contain any inst_names, any recursion has to be in the list
                // elements, and will be caught and handled there.
                match (inst1, inst2) with
                | (BoundCtor _, BoundCtor _) -> mergeInst2 inst1 inst2 maybeType
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
                            let result = mergeInst1 (inst1, inst2, maybeType)

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

            // The merge_inst_table has two functions. One is to act as a cache,
            // in the expectation that just looking up Inst would be quicker than
            // computing it. The other is to ensure termination for situations
            // in which one or both of InstA and InstB are recursive.
            match inst1, inst2 with
            | (Bound _, Free)
            | (Free, Bound _)
            | (Free, Free) -> None
            | Bound boundInst1, Bound boundInst2 ->
                mergeInst1 (boundInst1, boundInst2, maybeType)
                |> Option.map Bound

        member this.maybeAnyToBound(maybeType: System.Type option) : (BoundInstE option) = None

        member this.makeBoundInst(boundInsts: BoundCtorInstE list) : BoundInstE =
            let defaultDetails =
                { BoundInsts = boundInsts
                  TestResults = InstTestResults.noResults }

            let groundness =
                if (this.boundInstListIsGround (defaultDetails)) then
                    InstIsGround.IsGround
                else
                    InstIsGround.ContainsAny

            let instNames = HashSet<InstName> ()
            this.boundInstListContainedInstNames (HashSet<InstName> (), instNames, defaultDetails)

            let testResults =
                { Groundness = groundness
                  ContainsInstNames = ContainsInstNames instNames }

            let orderedInsts =
                boundInsts |> List.sortBy (fun b -> b.Constructor)

            BoundCtor
                { BoundInsts = orderedInsts
                  TestResults = testResults }

        member this.makeBoundInst(ctor: Constructor, argInsts: BoundInstE list) : BoundInstE =
            this.makeBoundInst (
                [ { Constructor = ctor
                    ArgInsts = argInsts } ]
            )

    let rec ofInst instTable (inst: Inst) : InstE =
        match inst with
        | Inst.Bound boundInst -> InstE.Bound (ofBoundInst instTable boundInst)
        | Inst.Free -> InstE.Free

    and ofBoundInst (instTable: InstTable) (inst: BoundInst) : BoundInstE =
        match inst with
        | BoundInst.Ground -> BoundInstE.Ground
        | BoundInst.Any -> BoundInstE.Any
        | BoundInst.NotReached -> BoundInstE.NotReached
        | BoundInst.HigherOrder (mode) ->
            let modes =
                List.map (fun (inst1, inst2) -> (ofInst instTable inst1, ofBoundInst instTable inst2)) mode.Modes

            BoundInstE.HigherOrder
                { Modes = modes
                  Determinism = mode.Determinism }
        | BoundInst.BoundCtor (boundInsts) -> instTable.makeBoundInst (List.map (ofBoundCtorInst instTable) boundInsts)

    and ofBoundCtorInst instTable (boundInst: BoundCtorInst) : BoundCtorInstE =
        { Constructor = boundInst.Constructor
          ArgInsts = (List.map (ofBoundInst instTable) boundInst.ArgInsts) }
