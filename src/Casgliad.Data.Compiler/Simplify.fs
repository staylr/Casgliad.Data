namespace Casgliad.Data.Compiler

module internal Simplify =
    let rec internal flattenConjunction' flattenedGoals (goal: Goal) =
        match goal.Goal with
        | Conjunction goals -> List.fold flattenConjunction' flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let flattenConjunction (goals: Goal list) =
        let flattenedGoals =
            List.fold flattenConjunction' [] goals |> List.rev

        match flattenedGoals with
        | [ singleGoal ] -> singleGoal.Goal
        | _ -> Conjunction (flattenedGoals)

    let rec internal flattenDisjunction' flattenedGoals (goal: Goal) =
        match goal.Goal with
        | Disjunction goals -> List.fold flattenDisjunction' flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let flattenDisjunction (goals: Goal list) =
        let flattenedGoals =
            List.fold flattenDisjunction' [] goals |> List.rev

        match flattenedGoals with
        | [ singleGoal ] -> singleGoal.Goal
        | _ -> Disjunction (flattenedGoals)


    let excessAssignsInConj goals nonLocals (varSet: VarSet) =
        let rec findRenamedVar (substitution: Map<VarId, VarId>) (var: VarId) =
            match Map.tryFind var substitution with
            | Some var' -> findRenamedVar substitution var'
            | None -> var

        let goalIsExcessAssign (remainingGoals: ResizeArray<Goal>) substitution goal =
            let addSubstitution eliminateVar replacementVar =
                Map.add eliminateVar replacementVar substitution

            match goal.Goal with
            | Unify (lhs0, Var (rhs0, VarVarUnifyType.Assign), _, _) ->
                let lhs = findRenamedVar substitution lhs0
                let rhs = findRenamedVar substitution rhs0
                let canEliminateLeft = not (TagSet.contains lhs nonLocals)
                let canEliminateRight = not (TagSet.contains rhs nonLocals)

                match canEliminateLeft, canEliminateRight with
                | true, true ->
                    if (varSet.varIsNamed (lhs)) then
                        addSubstitution lhs rhs
                    else
                        addSubstitution rhs lhs
                | true, false -> addSubstitution lhs rhs
                | false, true -> addSubstitution rhs lhs
                | false, false ->
                    remainingGoals.Add (goal)
                    substitution
            | _ ->
                remainingGoals.Add (goal)
                substitution

        let goalArray = ResizeArray<Goal> ()

        let substitution =
            goals
            |> List.fold (goalIsExcessAssign goalArray) Map.empty

        if (Map.isEmpty substitution) then
            goals
        else
            let substitution' =
                Map.map (fun _ v -> findRenamedVar substitution v) substitution

            goalArray
            |> Seq.map (renameVars substitution' false)
            |> List.ofSeq

    let rec internal simplifyGoal (varSet: VarSet) (goal: Goal) =
        match goal.Goal with
        | Unify _
        | Call _
        | FSharpCall _ -> goal
        | Conjunction goals ->
            let flattenedGoal = flattenConjunction goals

            match flattenedGoal with
            | Conjunction (goals) ->
                let goals' =
                    excessAssignsInConj goals (goal.Info.NonLocals) varSet

                match goals' with
                | [ singleGoal ] -> { goal with Goal = singleGoal.Goal }
                | _ ->
                    { goal with
                          Goal = Conjunction (goals |> List.map (simplifyGoal varSet)) }
            | _ -> simplifyGoal varSet { goal with Goal = flattenedGoal }
        | Disjunction goals ->
            let flattenedGoal = flattenDisjunction goals

            match flattenedGoal with
            | Disjunction (goals) ->
                { goal with
                      Goal = Disjunction (goals |> List.map (simplifyGoal varSet)) }
            | _ -> simplifyGoal varSet { goal with Goal = flattenedGoal }
        | Not negGoal ->
            { goal with
                  Goal = Not (simplifyGoal varSet negGoal) }
        | Scope (reason, scopeGoal) ->
            { goal with
                  Goal = Scope (reason, simplifyGoal varSet scopeGoal) }
        | IfThenElse (condGoal, thenGoal, elseGoal) ->
            let condGoal' = simplifyGoal varSet condGoal
            let thenGoal' = simplifyGoal varSet thenGoal
            let elseGoal' = simplifyGoal varSet elseGoal

            match elseGoal'.Goal with
            | Fail _ ->
                // TODO - sequential conjunction.
                { goal with
                      Goal = Conjunction ([ condGoal'; thenGoal' ]) }
            | _ ->
                match condGoal'.Goal with
                | Fail _ ->
                    // TODO: fix determinism of Not goal.
                    { goal with
                          Goal =
                              Conjunction (
                                  [ { Goal = Not (condGoal')
                                      Info = condGoal'.Info }
                                    elseGoal' ]
                              ) }
                | _ ->
                    { goal with
                          Goal = IfThenElse (condGoal', thenGoal', elseGoal') }

        | Switch (var, canFail, cases) ->
            { goal with
                  Goal =
                      Switch (
                          var,
                          canFail,
                          List.map
                              (fun case ->
                                  { case with
                                        CaseGoal = simplifyGoal varSet case.CaseGoal })
                              cases
                      ) }
