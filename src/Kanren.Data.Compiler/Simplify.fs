namespace Kanren.Data.Compiler

module Simplify =
    let rec internal flattenConjunction flattenedGoals (goal: Goal) =
        match goal.goal with
        | Conj goals -> List.fold flattenConjunction flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let rec internal flattenDisjunction flattenedGoals (goal: Goal) =
        match goal.goal with
        | Disj goals -> List.fold flattenDisjunction flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let rec internal simplifyGoal (goal: Goal) =
        match goal.goal with
        | Unify (_, _) -> goal
        | Call (_, _) -> goal
        | FSharpCall(_, _, _) -> goal
        | Conj goals ->
            { goal with goal = Conj (List.fold flattenConjunction [] goals |> List.rev |> List.map simplifyGoal) }
        | Disj goals ->
            { goal with goal = Disj (List.fold flattenDisjunction [] goals |> List.rev |> List.map simplifyGoal) }
        | Not negGoal ->
            { goal with goal = Not (simplifyGoal negGoal) }
        | IfThenElse(condGoal, thenGoal, elseGoal, existVars) ->
            let condGoal' = simplifyGoal condGoal
            let thenGoal' = simplifyGoal thenGoal
            let elseGoal' = simplifyGoal elseGoal
            match elseGoal'.goal with
            | Fail _ ->
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
