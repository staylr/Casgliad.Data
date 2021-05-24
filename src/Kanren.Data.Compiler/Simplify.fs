namespace Kanren.Data.Compiler

module Simplify =
    let rec internal flattenConjunction' flattenedGoals (goal: Goal) =
        match goal.goal with
        | Conj goals -> List.fold flattenConjunction' flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let flattenConjunction (goals: Goal list) =
        let flattenedGoals = List.fold flattenConjunction' [] goals |> List.rev
        match flattenedGoals with
        | [singleGoal] -> singleGoal.goal
        | _ -> Conj(flattenedGoals)

    let rec internal flattenDisjunction' flattenedGoals (goal: Goal) =
        match goal.goal with
        | Disj goals -> List.fold flattenDisjunction' flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let flattenDisjunction (goals: Goal list) =
        let flattenedGoals = List.fold flattenDisjunction' [] goals |> List.rev
        match flattenedGoals with
        | [singleGoal] -> singleGoal.goal
        | _ -> Disj(flattenedGoals)

    let rec internal simplifyGoal (goal: Goal) =
        match goal.goal with
        | Unify (_, _, _, _) -> goal
        | Call (_, _) -> goal
        | FSharpCall(_, _, _) -> goal
        | Conj goals ->
            let flattenedGoal = flattenConjunction goals
            match flattenedGoal with
            | Conj(goals) ->
                { goal with goal = Conj( goals |> List.map simplifyGoal) }
            | _ ->
                simplifyGoal { goal with goal = flattenedGoal }
        | Disj goals ->
             let flattenedGoal = flattenDisjunction goals
             match flattenedGoal with
             | Disj(goals) ->
                 { goal with goal = Disj( goals |> List.map simplifyGoal) }
             | _ ->
                 simplifyGoal { goal with goal = flattenedGoal }
        | Not negGoal ->
            { goal with goal = Not (simplifyGoal negGoal) }
        | IfThenElse(condGoal, thenGoal, elseGoal, existVars) ->
            let condGoal' = simplifyGoal condGoal
            let thenGoal' = simplifyGoal thenGoal
            let elseGoal' = simplifyGoal elseGoal
            match elseGoal'.goal with
            | Fail _ ->
                // TODO - sequential conjunction.
                { goal with goal = Conj([condGoal'; thenGoal']) }
            | _ ->
                match condGoal'.goal with
                | Fail _ ->
                    // TODO: fix determinism of Not goal.
                    { goal with goal = Conj([{ goal = Not(condGoal'); info = condGoal'.info}; elseGoal'])}
                | _ ->
                    { goal with goal = IfThenElse(condGoal', thenGoal', elseGoal', existVars)}

        | Switch (var, canFail, cases) ->
            { goal with goal =  Switch (var, canFail, List.map (fun case -> { case with caseGoal = simplifyGoal case.caseGoal }) cases) }
