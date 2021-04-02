namespace Kanren.Data.Compiler

open Kanren.Data

module Compile =

    let internal compile (relation : 'A Relation) =
        List.map (QuotationParser.translateExpr None) relation.Clauses
        |> fun g -> { goal = Disj g; info = GoalInfo.init None }
        |> Simplify.simplifyGoal

