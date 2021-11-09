namespace Kanren.Data.Compiler

open System.Collections.Generic

module internal InstMatch =

    type AnyMatchesAny =
    | AnyMatchesAny
    | AnyDoesNotMatchAny

    // inst_matches_final(InstA, InstB, MaybeType):
    //
    // Succeed iff InstA is compatible with InstB, i.e. iff InstA will satisfy
    // the final inst requirement InstB. This is true if the information
    // specified by InstA is at least as great as that specified by InstB,
    // and where the information is the same and both insts specify a binding,
    // the binding must be identical.
    let rec instMatchesFinal (instTable: InstTable) (inst1: InstE) (inst2: InstE) (maybeType: System.Type option) : bool =
        let rec instMatchesFinal3 expanded inst1 inst2 maybeType =
            match inst1 with
            | Any ->
                match inst2 with
                | Any ->
                    true
                | NotReached | HigherOrder _ | HigherOrderAny _ | DefinedInst _ ->
                    false
                | Ground | BoundCtor _ ->
                    match instTable.maybeAnyToBound(maybeType) with
                    | Some inst1' ->
                        instMatchesFinal2 expanded inst1' inst2 maybeType
                    | None ->
                        false
            | BoundCtor (boundInsts1) ->
                match inst2 with
                | Any ->
                    true
                | BoundCtor (boundInsts2) ->
                    boundInstListMatchesFinal expanded boundInsts1.BoundInsts boundInsts2.BoundInsts maybeType
                | Ground ->
                    instTable.boundInstListIsGround (boundInsts1)
                | DefinedInst _ | HigherOrder _ | HigherOrderAny _ | NotReached->
                    false
            | Ground ->
                match inst2 with
                | Ground | Any ->
                    true
                | BoundCtor (boundInsts2) ->
                    match maybeType with
                    | Some instType ->
                        instTable.boundInstListIsCompleteForType((HashSet<InstName>()), boundInsts2.BoundInsts, instType)
                            && groundMatchesFinalBoundInstList expanded boundInsts2 maybeType
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

        and instMatchesFinal2 (expanded: HashSet<InstMatchInputs>) (inst1: BoundInstE) (inst2: BoundInstE) maybeType =
            let input = { Inst1 = inst1; Inst2 = inst2; Type = maybeType }
            // TODO: HashSet isn't the right data structure. Want to use Set, but InstE is not comparable.
            if (expanded.Contains(input)) then
                true
            else
                let expanded' = HashSet<InstMatchInputs>(expanded)
                do expanded'.Add(input) |> ignore
                let inst1' = instTable.expand(inst1)
                let inst2' = instTable.expand(inst2)
                instMatchesFinal3 expanded' inst1' inst2' maybeType

        and instMatchesFinal1 (expanded: HashSet<InstMatchInputs>) inst1 inst2 maybeType =
            match (inst1, inst2) with
            | (Free, Free) -> true
            | (Free, Bound _) -> false
            | (Bound boundInst1, Free) ->
                boundInst1 <> NotReached
            | (Bound boundInst1, Bound boundInst2) ->
                instMatchesFinal2 expanded boundInst1 boundInst2 maybeType

        // Assumes that the check of `bound_inst_list_is_complete_for_type' is done by the caller.
        and groundMatchesFinalBoundInstList expanded boundInsts maybeType =
            boundInsts.BoundInsts
            |> List.forall (fun boundInst ->
                                let argTypes = InstTable.maybeGetConsIdArgTypes(maybeType, boundInst.Constructor)
                                List.forall2 (instMatchesFinal2 expanded Ground)
                                        boundInst.ArgInsts argTypes
                           )

        // Here we check that the functors in the first list are a subset of the
        // functors in the second list. (If a bound(...) inst only specifies the
        // insts for some of the constructors of its type, then it implicitly means
        // that all other constructors must have all their arguments `not_reached'.)
        // The code here makes use of the fact that the bound_inst lists are sorted.
        and boundInstListMatchesFinal
                (expanded: HashSet<InstMatchInputs>)
                (boundInsts1: BoundCtorInstE list)
                (boundInsts2: BoundCtorInstE list)
                maybeType =
            match (boundInsts1, boundInsts2) with
            | ([], _) ->
                true
            | (boundInst1 :: boundInsts1', boundInst2 :: boundInsts2') ->
                if (boundInst1.Constructor = boundInst2.Constructor) then
                    let argTypes = InstTable.maybeGetConsIdArgTypes(maybeType, boundInst1.Constructor)
                    forall3 (instMatchesFinal2 expanded) boundInst1.ArgInsts boundInst2.ArgInsts argTypes
                elif (boundInst1.Constructor > boundInst2.Constructor) then
                    boundInstListMatchesFinal expanded boundInsts1 boundInsts2' maybeType
                else
                    false
            | _ ->
                false

        and higherOrderInstInfoMatches (hoInst1: RelationModeE) (hoInst2: RelationModeE) maybeType : bool =
            let higherOrderArgModeMatches (mode1: ModeE) (mode2: ModeE) (maybeType: System.Type option) =
                instMatchesFinal instTable (fst mode2) (fst mode1) maybeType
                    && instMatchesFinal instTable (snd mode1 |> Bound) (snd mode2 |> Bound) maybeType

            hoInst1.Determinism = hoInst2.Determinism
            &&
                let argTypes = InstTable.maybeGetHigherOrderArgTypes (maybeType, hoInst1.Modes.Length)
                forall3 higherOrderArgModeMatches hoInst1.Modes hoInst2.Modes argTypes

        instMatchesFinal1 (HashSet<InstMatchInputs>()) inst1 inst2 maybeType

    // inst_matches_binding(InstA, InstB, MaybeType):
    //
    // Succeed iff the binding of InstA is definitely exactly the same as
    // that of InstB. This is the same as inst_matches_final except that it
    // ignores uniqueness, and that `any' does not match itself. It is used
    // to check whether variables get bound in negated contexts.
    let instMatchesBinding (instTable: InstTable) (inst1: InstE) (inst2: InstE) (maybeType: System.Type option) (anyMatchesAny: AnyMatchesAny) : bool =
        let rec instMatchesBinding3 expanded inst1 inst2 maybeType =
            match inst1 with
            | Any ->
                match inst2 with
                | Any ->
                    match AnyMatchesAny with
                    | AnyMatchesAny ->
                        true
                    | AnyDoesNotMatchAny ->
                        match inst2 with
                        | Any ->
                            true
                        | NotReached | HigherOrder _ | HigherOrderAny _ | DefinedInst _ ->
                            false
                        | Ground | BoundCtor _ ->
                            match instTable.maybeAnyToBound(maybeType) with
                            | Some inst1' ->
                                instMatchesBinding2 expanded inst1' inst2 maybeType
                            | None ->
                                false
                | Ground | BoundCtor _ ->
                    match instTable.maybeAnyToBound(maybeType) with
                    | Some inst1' ->
                        instMatchesBinding2 expanded inst1' inst2 maybeType
                    | None ->
                        false
            | BoundCtor (boundInsts1) ->
                match inst2 with
                | Any ->
                    match instTable.maybeAnyToBound(maybeType) with
                    | Some inst2' ->
                        instMatchesBinding2 expanded inst1 inst2' maybeType
                    | None ->
                        false
                | BoundCtor (boundInsts2) ->
                    boundInstListMatchesBinding expanded boundInsts1.BoundInsts boundInsts2.BoundInsts maybeType
                | Ground ->
                    instTable.boundInstListIsGround (boundInsts1)
                | DefinedInst _ | HigherOrder _ | HigherOrderAny _ | NotReached->
                    false
            | Ground ->
                match inst2 with
                | Ground ->
                    true
                | Any ->
                    match instTable.maybeAnyToBound(maybeType) with
                    | Some inst2' ->
                        instMatchesBinding2 expanded inst1 inst2' maybeType
                    | None ->
                        false
                | BoundCtor (boundInsts2) ->
                    match maybeType with
                    | Some instType ->
                        instTable.boundInstListIsCompleteForType((HashSet<InstName>()), boundInsts2.BoundInsts, instType)
                            && groundMatchesBindingBoundInstList expanded boundInsts2 maybeType
                    | None ->
                        false
                | DefinedInst _ | HigherOrder _ | HigherOrderAny _ | NotReached ->
                    false
            | HigherOrder info1 ->
                match inst2 with
                | HigherOrder info2 ->
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

        and instMatchesBinding2 (expanded: HashSet<InstMatchInputs>) (inst1: BoundInstE) (inst2: BoundInstE) maybeType =
            let input = { Inst1 = inst1; Inst2 = inst2; Type = maybeType }
            // TODO: HashSet isn't the right data structure. Want to use Set, but InstE is not comparable.
            if (expanded.Contains(input)) then
                true
            else
                let expanded' = HashSet<InstMatchInputs>(expanded)
                do expanded'.Add(input) |> ignore
                let inst1' = instTable.expand(inst1)
                let inst2' = instTable.expand(inst2)
                instMatchesBinding3 expanded' inst1' inst2' maybeType

        and instMatchesBinding1 (expanded: HashSet<InstMatchInputs>) inst1 inst2 maybeType =
            match (inst1, inst2) with
            | (Free, Free) -> true
            | (Free, Bound _) -> false
            | (Bound boundInst, Free) -> boundInst = NotReached
            | (Bound boundInst1, Bound boundInst2) ->
                instMatchesBinding2 expanded boundInst1 boundInst2 maybeType

        // Assumes that the check of `bound_inst_list_is_complete_for_type' is done by the caller.
        and groundMatchesBindingBoundInstList expanded boundInsts maybeType =
            boundInsts.BoundInsts
            |> List.forall (fun boundInst ->
                                let argTypes = InstTable.maybeGetConsIdArgTypes(maybeType, boundInst.Constructor)
                                List.forall2 (instMatchesBinding2 expanded Ground)
                                        boundInst.ArgInsts argTypes
                           )

        // Here we check that the functors in the first list are a subset of the
        // functors in the second list. (If a bound(...) inst only specifies the
        // insts for some of the constructors of its type, then it implicitly means
        // that all other constructors must have all their arguments `not_reached'.)
        // The code here makes use of the fact that the bound_inst lists are sorted.
        and boundInstListMatchesBinding
                (expanded: HashSet<InstMatchInputs>)
                (boundInsts1: BoundCtorInstE list)
                (boundInsts2: BoundCtorInstE list)
                maybeType =
            match (boundInsts1, boundInsts2) with
            | ([], _) ->
                true
            | (boundInst1 :: boundInsts1', boundInst2 :: boundInsts2') ->
                if (boundInst1.Constructor = boundInst2.Constructor) then
                    let argTypes = InstTable.maybeGetConsIdArgTypes(maybeType, boundInst1.Constructor)
                    forall3 (instMatchesBinding2 expanded) boundInst1.ArgInsts boundInst2.ArgInsts argTypes
                elif (boundInst1.Constructor > boundInst2.Constructor) then
                    boundInstListMatchesBinding expanded boundInsts1 boundInsts2' maybeType
                else
                    false
            | _ ->
                false

        and higherOrderInstInfoMatches (hoInst1: RelationModeE) (hoInst2: RelationModeE) maybeType : bool =
            let higherOrderArgModeMatches (mode1: ModeE) (mode2: ModeE) (maybeType: System.Type option) =
                instMatchesFinal instTable (fst mode2) (fst mode1) maybeType
                    && instMatchesFinal instTable (snd mode1 |> Bound) (snd mode2 |> Bound) maybeType

            hoInst1.Determinism = hoInst2.Determinism
            &&
                let argTypes = InstTable.maybeGetHigherOrderArgTypes (maybeType, hoInst1.Modes.Length)
                forall3 higherOrderArgModeMatches hoInst1.Modes hoInst2.Modes argTypes

        instMatchesBinding1 (HashSet<InstMatchInputs>()) inst1 inst2 maybeType


    // inst_matches_initial(InstA, InstB, MaybeType):
    //
    // Succeed iff `InstA' specifies at least as much information as `InstB',
    // and in those parts where they specify the same information, `InstA'
    // is at least as instantiated as `InstB'. Thus, the call
    // inst_matches_initial(not_reached, ground, _) succeeds, since
    // not_reached contains more information than ground - but not vice versa.
    // Similarly, inst_matches_initial(bound(a), bound(a;b), _) should
    // succeed, but not vice versa.
    let instMatchesInitial (instTable: InstTable) (inst1: InstE) (inst2: InstE) (maybeType: System.Type option) : bool =
        let rec instMatchesInitial3 expanded inst1 inst2 maybeType =
            match inst1 with
            | Any ->
                match inst2 with
                | Any ->
                    true
                | NotReached | HigherOrder _ | HigherOrderAny _ | DefinedInst _ ->
                    false
                | Ground | BoundCtor _ ->
                    match instTable.maybeAnyToBound(maybeType) with
                    | Some inst1' ->
                        instMatchesInitial2 expanded inst1' inst2 maybeType
                    | None ->
                        false
            | BoundCtor (boundInsts1) ->
                match inst2 with
                | Any ->
                    true
                | BoundCtor (boundInsts2) ->
                    boundInstListMatchesInitial expanded boundInsts1.BoundInsts boundInsts2.BoundInsts maybeType
                | Ground ->
                    instTable.boundInstListIsGround (boundInsts1)
                | DefinedInst _ | HigherOrder _ | HigherOrderAny _ | NotReached->
                    false
            | Ground ->
                match inst2 with
                | Ground | Any ->
                    true
                | BoundCtor (boundInsts2) ->
                    match maybeType with
                    | Some instType ->
                        instTable.boundInstListIsCompleteForType((HashSet<InstName>()), boundInsts2.BoundInsts, instType)
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

        and instMatchesInitial2 (expanded: HashSet<InstMatchInputs>) (inst1: BoundInstE) (inst2: BoundInstE) maybeType =
            let input = { Inst1 = inst1; Inst2 = inst2; Type = maybeType }
            // TODO: HashSet isn't the right data structure. Want to use Set, but InstE is not comparable.
            if (expanded.Contains(input)) then
                true
            else
                let expanded' = HashSet<InstMatchInputs>(expanded)
                do expanded'.Add(input) |> ignore
                let inst1' = instTable.expand(inst1)
                let inst2' = instTable.expand(inst2)
                instMatchesInitial3 expanded' inst1' inst2' maybeType

        and instMatchesInitial1 (expanded: HashSet<InstMatchInputs>) inst1 inst2 maybeType =
            match (inst1, inst2) with
            | (Free, Free) -> true
            | (Free, Bound _) -> false
            | (Bound boundInst1, Free) ->
                boundInst1 <> NotReached
            | (Bound boundInst1, Bound boundInst2) ->
                instMatchesInitial2 expanded boundInst1 boundInst2 maybeType

        // Assumes that the check of `bound_inst_list_is_complete_for_type' is done by the caller.
        and groundMatchesInitialBoundInstList expanded boundInsts maybeType =
            boundInsts.BoundInsts
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
                (boundInsts1: BoundCtorInstE list)
                (boundInsts2: BoundCtorInstE list)
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
                instMatchesFinal instTable (fst mode2) (fst mode1) maybeType
                    && instMatchesFinal instTable (snd mode1 |> Bound) (snd mode2 |> Bound) maybeType

            hoInst1.Determinism = hoInst2.Determinism
            &&
                let argTypes = InstTable.maybeGetHigherOrderArgTypes (maybeType, hoInst1.Modes.Length)
                forall3 higherOrderArgModeMatches hoInst1.Modes hoInst2.Modes argTypes

        instMatchesInitial1 (HashSet<InstMatchInputs>()) inst1 inst2 maybeType
