namespace Kanren.Data.Compiler

open Kanren.Data.Compiler.State

module Quantification =
    let q = 0

    type QInfo = {
            VarSet: VarSet;
            Seen: SetOfVar;
            Outside: SetOfVar;
            LambdaOutside: SetOfVar;
            Quantified: SetOfVar;
            NonLocals: SetOfVar
        }
    
    let state = new StateBuilder()

    let seen info = (info.Seen, info)
    let quantVars info = (info.Quantified, info)
    let setQuantVars vars info = ((), { info with Quantified = vars })
    let nonLocals info = (info.NonLocals, info)
    let setNonLocals vars info = ((), { info with NonLocals = vars })
    let outside info = (info.Outside, info)
    let setOutside vars info = ((), { info with Outside = vars })
    let lambdaOutside info = (info.LambdaOutside, info)
    let setLambdaOutside vars info = ((), { info with LambdaOutside = vars })
    let updateSeenVars vars info = ((), { info with Seen = TagSet.ofList vars |> TagSet.union info.Seen })
    let updateSeenVarsSet vars info = ((), { info with Seen = TagSet.union info.Seen vars })

    let rec quantifyGoal goal = 
        state {
            let! initialSeen = seen
            let! (goal', possibleNonLocals) = quantifyGoalExpr goal.goal goal.info
            let! nonLocals = nonLocals
            let localVars = TagSet.difference possibleNonLocals nonLocals
            let renameVars = TagSet.intersect initialSeen localVars

            // Rename apart local variables that we have seen elsewhere, e.g. in other disjuncts.
            //let! goal'' =
            //    if (TagSet.isEmpty renameVars) then
            //        goal'
            //    else
            //        renameApart renameVars goal'
            return ({ goal = goal'; info = { goal.info with nonLocals = nonLocals }})
        }

    and quantifyGoalExpr goalExpr goalInfo =
        state {
            let! initialOutside = outside
            let! initialLmabdaOutside = lambdaOutside
            match goalExpr with
            | Unify(lhs, rhs, mode, context) ->
                return! quantifyUnify lhs rhs mode context goalInfo
        }

    and quantifyUnify lhs rhs mode context goalInfo =
        state {
            let! (rhs', rhsVars) = quantifyUnifyRhs rhs goalInfo
            let! outside = outside
            let! lambdaOutside = lambdaOutside
            let goalExpr = Unify (lhs, rhs', mode, context)
            let goalVars = TagSet.add lhs rhsVars
            do! updateSeenVarsSet goalVars
            let outsideNonLocals = TagSet.intersect goalVars outside
            let lambdaOutsideNonLocals = TagSet.intersect goalVars lambdaOutside
            let nonLocals = TagSet.union outsideNonLocals lambdaOutsideNonLocals
            do! setNonLocals nonLocals
            return (goalExpr, goalVars)
        }
    
    and quantifyUnifyRhs rhs goalInfo =
        state {
            match rhs with
            | Var (rhsVar, uType) -> return (rhs, TagSet.singleton rhsVar)
            | Constructor (_, args, _, _) -> return (rhs, TagSet.ofList args)
            | Lambda (lambdaNonLocals, lambdaVars, modes, det, goal) ->
                let! outside = outside
                let! qvars = quantVars
                let! lambdaOutside = lambdaOutside

                let lambdaVarsSet = TagSet.ofList lambdaVars

                // Quantified variables cannot be pushed inside a lambda goal,
                // so we insert the quantified vars into the outside vars set,
                // and initialize the new quantified vars set to be empty.
                do! setQuantVars TagSet.empty
                do! setOutside (TagSet.union outside qvars |> TagSet.union lambdaVarsSet)

                // Set the LambdaOutsideVars set to empty, because variables that occur
                // outside this lambda expression only in other lambda expressions
                // should not be considered nonlocal.
                do! setLambdaOutside TagSet.empty
                
                let! goal' = quantifyGoal goal

                let! rhsNonLocals = nonLocals
                let rhsNonLocals' = TagSet.difference rhsNonLocals lambdaVarsSet

                do! setQuantVars qvars
                do! setOutside outside
                do! setLambdaOutside lambdaOutside

                // Work out the list of nonlocal curried arguments to the lambda
                // expression. This set must only ever decrease, since the first
                // approximation that make_hlds uses includes all variables in the
                // lambda expression except the quantified variables.
                let lambdaGoalNonLocals = goal'.info.nonLocals
                let lambdaNonLocals' = List.filter (fun v -> TagSet.contains v lambdaGoalNonLocals) lambdaNonLocals
                return (rhs, rhsNonLocals')
        }

    let implicitlyQuantifyGoal (args: VarId list) (varset: VarSet) (goal: Goal) =
        let info = { VarSet = varset;
                    Seen = emptySetOfVar;
                    Outside = TagSet.ofList args;
                    LambdaOutside = emptySetOfVar;
                    Quantified =  emptySetOfVar;
                    NonLocals = emptySetOfVar }
        let (goal, info') = State.run (quantifyGoal goal) info
        (goal, info'.VarSet)
