namespace Kanren.Data.Compiler

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
        | _ -> Conjunction(flattenedGoals)

    let rec internal flattenDisjunction' flattenedGoals (goal: Goal) =
        match goal.Goal with
        | Disjunction goals -> List.fold flattenDisjunction' flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let flattenDisjunction (goals: Goal list) =
        let flattenedGoals =
            List.fold flattenDisjunction' [] goals |> List.rev

        match flattenedGoals with
        | [ singleGoal ] -> singleGoal.Goal
        | _ -> Disjunction(flattenedGoals)

    let rec internal simplifyGoal (goal: Goal) =
        match goal.Goal with
        | Unify _ | Call _ | FSharpCall _ -> goal
        | Conjunction goals ->
            let flattenedGoal = flattenConjunction goals

            match flattenedGoal with
            | Conjunction (goals) ->
                { goal with
                      Goal = Conjunction(goals |> List.map simplifyGoal) }
            | _ -> simplifyGoal { goal with Goal = flattenedGoal }
        | Disjunction goals ->
            let flattenedGoal = flattenDisjunction goals

            match flattenedGoal with
            | Disjunction (goals) ->
                { goal with
                      Goal = Disjunction(goals |> List.map simplifyGoal) }
            | _ -> simplifyGoal { goal with Goal = flattenedGoal }
        | Not negGoal ->
            { goal with
                  Goal = Not(simplifyGoal negGoal) }
        | IfThenElse (condGoal, thenGoal, elseGoal) ->
            let condGoal' = simplifyGoal condGoal
            let thenGoal' = simplifyGoal thenGoal
            let elseGoal' = simplifyGoal elseGoal

            match elseGoal'.Goal with
            | Fail _ ->
                // TODO - sequential conjunction.
                { goal with
                      Goal = Conjunction([ condGoal'; thenGoal' ]) }
            | _ ->
                match condGoal'.Goal with
                | Fail _ ->
                    // TODO: fix determinism of Not goal.
                    { goal with
                          Goal =
                              Conjunction(
                                  [ { Goal = Not(condGoal')
                                      Info = condGoal'.Info }
                                    elseGoal' ]
                              ) }
                | _ ->
                    { goal with
                          Goal = IfThenElse(condGoal', thenGoal', elseGoal') }

        | Switch (var, canFail, cases) ->
            { goal with
                  Goal =
                      Switch(
                          var,
                          canFail,
                          List.map
                              (fun case ->
                                  { case with
                                        CaseGoal = simplifyGoal case.CaseGoal })
                              cases
                      ) }
