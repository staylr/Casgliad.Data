namespace Kanren.Data

open Kanren.Data
open FSharp.Data.Sql
open FSharp.Quotations

type varid = int

type 'A Var = Var of varid

type 'A Term = 
    | Var of 'A Var

module Main =

    let rec flattenConjunction flattenedGoals goal =
        match goal with
        | Conj goals -> List.fold flattenConjunction flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let rec flattenDisjunction flattenedGoals goal =
        match goal with
        | Disj goals -> List.fold flattenDisjunction flattenedGoals goals
        | _ -> goal :: flattenedGoals

    let rec simplifyGoal goal =
        match goal with
        | Unify (_, _, _) -> goal
        | Call (_, _) -> goal
        | Conj goals -> Conj (goals |> List.fold flattenConjunction [] |> List.rev |> List.map simplifyGoal)
        | Disj goals -> Disj (goals |> List.fold flattenDisjunction [] |> List.rev |> List.map simplifyGoal)
        | Exists (v, goal) -> Exists (v, simplifyGoal goal)
        | Not negGoal -> Not (simplifyGoal negGoal)

    let compile (relation : 'A Relation) =
        List.map QuotationParser.translateExpr relation.Clauses
        |> Disj
        |> simplifyGoal

    [<Relation("rel2")>]
    let rel2 = { Name = "rel2"; Clauses = [ <@ fun (x, y) -> x = 4 && y = 2 @> ] }

    [<Relation("rel")>]
    let rel = { Name = "rel"; Clauses = [ <@ fun (x, y, z) -> (x = 1 && y = 2 && z = 3 && call rel2 (x, z)) @> ] }
