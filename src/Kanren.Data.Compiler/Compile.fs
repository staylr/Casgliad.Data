namespace Kanren.Data.Compiler

open Kanren.Data

module Compile =

    let flip f x y =
        let (r, s) = f y x
        (s, r)

    let internal compile (relation : 'A Relation) =
        let varset = VarSet.init
        let varset' = List.fold QuotationParser.getVars varset relation.Clauses
        let parserInfo = { varset = varset'; errors = [] }
        let (clauseGoals, parserInfo'') = List.mapFold (flip (QuotationParser.translateExpr None)) parserInfo relation.Clauses
        let goal = { goal = Disj(clauseGoals); info = GoalInfo.init None }
        Simplify.simplifyGoal goal

