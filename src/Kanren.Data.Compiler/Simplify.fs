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
        | Switch (var, canFail, cases) ->
            { goal with goal =  Switch (var, canFail, List.map (fun case -> { case with caseGoal = simplifyGoal case.caseGoal }) cases) }
