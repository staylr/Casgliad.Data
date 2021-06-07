namespace Kanren.Data.Compiler

module Simplify =
    let rec internal flattenConjunction' flattenedGoals (goal: Goal) =
        match goal.Goal with
        | Conj goals -> List.fold flattenConjunction' flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let flattenConjunction (goals: Goal list) =
        let flattenedGoals =
            List.fold flattenConjunction' [] goals |> List.rev

        match flattenedGoals with
        | [ singleGoal ] -> singleGoal.Goal
        | _ -> Conj(flattenedGoals)

    let rec internal flattenDisjunction' flattenedGoals (goal: Goal) =
        match goal.Goal with
        | Disj goals -> List.fold flattenDisjunction' flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let flattenDisjunction (goals: Goal list) =
        let flattenedGoals =
            List.fold flattenDisjunction' [] goals |> List.rev

        match flattenedGoals with
        | [ singleGoal ] -> singleGoal.Goal
        | _ -> Disj(flattenedGoals)

    let rec internal simplifyGoal (goal: Goal) =
        match goal.Goal with
        | Unify (_, _, _, _) -> goal
        | Call (_, _) -> goal
        | FSharpCall (_, _, _) -> goal
        | Conj goals ->
            let flattenedGoal = flattenConjunction goals

            match flattenedGoal with
            | Conj (goals) ->
                { goal with
                      Goal = Conj(goals |> List.map simplifyGoal) }
            | _ -> simplifyGoal { goal with Goal = flattenedGoal }
        | Disj goals ->
            let flattenedGoal = flattenDisjunction goals

            match flattenedGoal with
            | Disj (goals) ->
                { goal with
                      Goal = Disj(goals |> List.map simplifyGoal) }
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
                      Goal = Conj([ condGoal'; thenGoal' ]) }
            | _ ->
                match condGoal'.Goal with
                | Fail _ ->
                    // TODO: fix determinism of Not goal.
                    { goal with
                          Goal =
                              Conj(
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
