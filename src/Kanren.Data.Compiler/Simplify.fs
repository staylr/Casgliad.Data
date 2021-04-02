namespace Kanren.Data.Compiler

module Simplify =
    let rec internal flattenConjunction flattenedGoals goal =
        match goal.goal with
        | Conj goals -> List.fold flattenConjunction flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let rec internal flattenDisjunction flattenedGoals goal =
        match goal.goal with
        | Disj goals -> List.fold flattenDisjunction flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let rec internal simplifyGoal goal =
        match goal.goal with
        | Unify (_, _, _) -> goal
        | Call (_, _) -> goal
        | Conj goals -> { goal with goal = Conj (goals |> List.fold flattenConjunction [] |> List.rev |> List.map simplifyGoal) }
        | Disj goals -> { goal with goal = Disj (goals |> List.fold flattenDisjunction [] |> List.rev |> List.map simplifyGoal) }
        | Exists (v, goal) -> { goal with goal = Exists (v, simplifyGoal goal) }
        | Not negGoal -> { goal with goal = Not (simplifyGoal negGoal) }
