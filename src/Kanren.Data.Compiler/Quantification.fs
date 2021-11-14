namespace Kanren.Data.Compiler

open Kanren.Data.Compiler.State

module internal Quantification =

    type QInfo =
        { VarSet: VarSet
          Seen: SetOfVar
          Outside: SetOfVar
          LambdaOutside: SetOfVar
          Quantified: SetOfVar
          NonLocals: SetOfVar }

    let state = new StateBuilder()

    let seen info = (info.Seen, info)
    let quantVars info = (info.Quantified, info)
    let setQuantVars vars info = ((), { info with Quantified = vars })
    let nonLocals info = (info.NonLocals, info)
    let setNonLocals vars (info: QInfo) = ((), { info with NonLocals = vars })
    let outside info = (info.Outside, info)
    let setOutside vars info = ((), { info with Outside = vars })
    let lambdaOutside info = (info.LambdaOutside, info)

    let setLambdaOutside vars info =
        ((), { info with LambdaOutside = vars })

    let updateSeenVars vars info =
        ((),
         { info with
               Seen = TagSet.ofList vars |> TagSet.union info.Seen })

    let updateSeenVarsSet vars info =
        ((),
         { info with
               Seen = TagSet.union info.Seen vars })


    let rec goalVarsBoth goal =
        goalExprVarsBoth goal.Goal emptySetOfVar emptySetOfVar

    and goalExprVarsBoth goal set lambdaSet =
        match goal with
        | Unify (lhs, rhs, _, _) -> unifyRhsVarsBoth rhs (TagSet.add lhs set) lambdaSet
        | Call (_, args) -> (TagSet.union set (TagSet.ofList args), lambdaSet)
        | FSharpCall (_, ret, args) -> (TagSet.union set (TagSet.ofList (consOption ret args)), lambdaSet)
        | Conjunction (goals)
        | Disjunction (goals) -> goalListVarsBoth goals set lambdaSet
        | Not (goal) -> goalExprVarsBoth goal.Goal set lambdaSet
        | Scope (_, goal) -> goalExprVarsBoth goal.Goal set lambdaSet
        | Switch (var, _, cases) -> caseListVarsBoth cases (TagSet.add var set) lambdaSet
        | IfThenElse (condGoal, thenGoal, elseGoal) ->
            let (condSet, condLambdaSet) = goalVarsBoth condGoal
            let (thenSet, thenLambdaSet) = goalVarsBoth thenGoal
            let (elseSet, elseLambdaSet) = goalVarsBoth elseGoal
            let condThenSet = TagSet.union condSet thenSet
            let condThenLambdaSet = TagSet.union condLambdaSet thenLambdaSet

            (TagSet.union set condThenSet
             |> TagSet.union elseSet,
             TagSet.union set condThenLambdaSet
             |> TagSet.union elseLambdaSet)

    and goalListVarsBoth goals set lambdaSet =
        let goalInListVars (set, lambdaSet) goal =
            goalExprVarsBoth goal.Goal set lambdaSet

        List.fold goalInListVars (set, lambdaSet) goals

    and caseListVarsBoth cases set lambdaSet =
        let caseInListVars (set, lambdaSet) (case: Case) =
            goalExprVarsBoth case.CaseGoal.Goal set lambdaSet

        List.fold caseInListVars (set, lambdaSet) cases

    and unifyRhsVarsBoth rhs set lambdaSet =
        match rhs with
        | Var (var, _) -> (TagSet.add var set, lambdaSet)
        | Constructor (ctor, args, _, _, _) -> (TagSet.ofList args |> TagSet.union set, lambdaSet)
        | Lambda (_, lambdaVars, _, _, goal) ->
            let (goalSet, goalLambdaSet) = goalVarsBoth goal

            let goalVars =
                TagSet.difference (TagSet.union goalSet goalLambdaSet) (TagSet.ofList lambdaVars)

            (set, TagSet.union lambdaSet goalVars)

    let getFollowingVars goals =
        let goalFollowingVars goal (set, lambdaSet) =
            let (set', lambdaSet') = goalVarsBoth goal
            (TagSet.union set set', TagSet.union lambdaSet lambdaSet')

        List.scanBack goalFollowingVars goals (emptySetOfVar, emptySetOfVar)
        |> List.tail

    let rec quantifyGoal goal =
        state {
            let! initialSeen = seen
            let! (goal', possibleNonLocals) = quantifyGoalExpr goal.Goal goal.Info
            let! nonLocals = nonLocals

            let localVars =
                TagSet.difference possibleNonLocals nonLocals
            // let renameVars = TagSet.intersect initialSeen localVars

            // Rename apart local variables that we have seen elsewhere, e.g. in other disjuncts.
            //let! goal'' =
            //    if (TagSet.isEmpty renameVars) then
            //        goal'
            //    else
            //        renameApart renameVars goal'
            return
                ({ Goal = goal'
                   Info = { goal.Info with NonLocals = nonLocals } })
        }

    and quantifyGoalExpr goalExpr goalInfo =
        state {
            match goalExpr with
            | Unify (lhs, rhs, mode, context) -> return! quantifyUnify lhs rhs mode context goalInfo
            | Call (_, args) -> return! quantifyPrimitiveGoal goalExpr args
            | FSharpCall (_, returnArg, args) -> return! quantifyPrimitiveGoal goalExpr (consOption returnArg args)
            | Conjunction (goals) -> return! quantifyConj goals
            | Disjunction (goals) -> return! quantifyDisj goals
            | Not (negGoal) -> return! quantifyNegation negGoal
            | Scope (reason, scopeGoal) -> return! quantifyScope reason scopeGoal
            | IfThenElse (condGoal, thenGoal, elseGoal) -> return! quantifyIfThenElse condGoal thenGoal elseGoal
            | Switch (var, canFail, cases) -> return! quantifySwitch var canFail cases
        }

    and quantifyScope reason scopeGoal =
        state {
                let! scopeGoal' = quantifyGoal scopeGoal
                let scope = Scope (reason, scopeGoal')
                return (scope, (goalExprVars (Scope (reason, scopeGoal)) emptySetOfVar))
        }

    and quantifySwitch var canFail cases =
        state {
            let mutable cases' = []
            let mutable nonLocalVars = emptySetOfVar

            for case in cases do
                let! goal' = quantifyGoal case.CaseGoal
                let! goalNonLocals = nonLocals
                nonLocalVars <- TagSet.union nonLocalVars goalNonLocals
                cases' <- { case with CaseGoal = goal' } :: cases'

            do! setNonLocals (TagSet.add var nonLocalVars)
            let switch = Switch (var, canFail, cases')
            return (switch, (goalExprVars (Switch (var, canFail, cases)) emptySetOfVar))
        }

    and quantifyNegation negGoal =
        state {
            // Quantified variables cannot be pushed inside a negation, so we insert
            // the quantified vars into the outside vars set, and initialize the new
            // quantified vars set to be empty (the lambda outside vars remain
            // unchanged).
            let! qvars = quantVars
            let! outside = outside
            do! setOutside (TagSet.union outside qvars)
            do! setQuantVars emptySetOfVar
            let! negGoal' = quantifyGoal negGoal
            do! setOutside outside
            do! setQuantVars qvars
            return (Not(negGoal'), goalVars negGoal' emptySetOfVar)
        }
    and quantifyIfThenElse condGoal thenGoal elseGoal =
        state {
            let! qvars = quantVars
            let! outside = outside
            let! lambdaOutside = lambdaOutside
            let (varsThen, lambdaVarsThen) = goalVarsBoth thenGoal

            do! setOutside (TagSet.union outside varsThen)
            do! setLambdaOutside (TagSet.union lambdaOutside lambdaVarsThen)
            let! condGoal' = quantifyGoal condGoal
            let! nonLocalsCond = nonLocals

            do! setOutside (TagSet.union outside nonLocalsCond)
            do! setLambdaOutside lambdaOutside
            let! thenGoal' = quantifyGoal thenGoal
            let! nonLocalsThen = nonLocals

            do! setOutside outside
            do! setLambdaOutside lambdaOutside
            let! elseGoal' = quantifyGoal elseGoal
            let! nonLocalsElse = nonLocals

            let nonLocalsIte =
                seq {
                    nonLocalsCond
                    nonLocalsThen
                    nonLocalsElse
                }
                |> TagSet.unionMany

            let nonLocalsOutside = TagSet.intersect outside nonLocalsIte

            let nonLocalsLambdaOutside =
                TagSet.intersect lambdaOutside nonLocalsIte

            do! setNonLocals (TagSet.union nonLocalsOutside nonLocalsLambdaOutside)

            let goalExpr =
                IfThenElse(condGoal', thenGoal', elseGoal')

            return (goalExpr, goalExprVars goalExpr emptySetOfVar)
        }

    and quantifyConj goals =
        state {
            let followingVars = getFollowingVars goals
            let combineFollowingVars vars (f, lf) = TagSet.union vars f |> TagSet.union lf

            let possibleNonLocals =
                List.fold combineFollowingVars emptySetOfVar followingVars

            let! goals = quantifyConjWithFollowing (List.zip goals followingVars)
            return (Conjunction(goals), possibleNonLocals)
        }

    and quantifyConjWithFollowing followingVarPairs =
        state {
            match followingVarPairs with
            | [] ->
                do! setNonLocals emptySetOfVar
                return []
            | (goal, (followingVars, lambdaFollowingVars)) :: fs ->
                let! outside = outside
                let! lambdaOutside = lambdaOutside
                do! setOutside (TagSet.union outside followingVars)
                do! setLambdaOutside (TagSet.union lambdaOutside lambdaFollowingVars)

                let! goal' = quantifyGoal goal
                let! nonLocals1 = nonLocals
                do! setOutside (TagSet.union outside nonLocals1)
                do! setLambdaOutside lambdaOutside

                let! goals = quantifyConjWithFollowing fs
                let! nonLocals2 = nonLocals

                let nonLocalsConj = TagSet.union nonLocals1 nonLocals2

                let nonLocals =
                    TagSet.union (TagSet.intersect nonLocalsConj outside) (TagSet.intersect nonLocalsConj lambdaOutside)

                do! setOutside outside
                do! setLambdaOutside lambdaOutside
                do! setNonLocals nonLocals
                return (goal' :: goals)
        }

    and quantifyDisj goals =
        state {
            let mutable goals' = []
            let mutable nonLocalVars = emptySetOfVar

            for goal in goals do
                let! goal' = quantifyGoal goal
                let! goalNonlocals = nonLocals
                nonLocalVars <- TagSet.union nonLocalVars goalNonlocals
                goals' <- goal' :: goals'

            return (Disjunction(List.rev goals'), (goalExprVars (Disjunction(goals')) emptySetOfVar))
        }

    and quantifyPrimitiveGoal goalExpr args =
        state {
            let argsSet = TagSet.ofList args
            do! updateSeenVarsSet argsSet
            let! outside = outside
            let! lambdaOutside = lambdaOutside

            let nonLocals =
                TagSet.union (TagSet.intersect argsSet outside) (TagSet.intersect argsSet lambdaOutside)

            do! setNonLocals nonLocals
            return (goalExpr, argsSet)
        }

    and quantifyUnify lhs rhs mode context goalInfo =
        state {
            let! (rhs', rhsVars) = quantifyUnifyRhs rhs goalInfo
            let! outside = outside
            let! lambdaOutside = lambdaOutside
            let goalExpr = Unify(lhs, rhs', mode, context)
            let goalVars = TagSet.add lhs rhsVars
            do! updateSeenVarsSet goalVars
            let outsideNonLocals = TagSet.intersect goalVars outside
            let lambdaOutsideNonLocals = TagSet.intersect goalVars lambdaOutside

            let nonLocals =
                TagSet.union outsideNonLocals lambdaOutsideNonLocals

            do! setNonLocals nonLocals
            return (goalExpr, goalVars)
        }

    and quantifyUnifyRhs rhs goalInfo =
        state {
            match rhs with
            | Var (rhsVar, uType) -> return (rhs, TagSet.singleton rhsVar)
            | Constructor (_, args, _, _, _) -> return (rhs, TagSet.ofList args)
            | Lambda (lambdaNonLocals, lambdaVars, modes, det, goal) ->
                let! outside = outside
                let! qvars = quantVars
                let! lambdaOutside = lambdaOutside

                let lambdaVarsSet = TagSet.ofList lambdaVars

                // Quantified variables cannot be pushed inside a lambda goal,
                // so we insert the quantified vars into the outside vars set,
                // and initialize the new quantified vars set to be empty.
                do! setQuantVars TagSet.empty

                do!
                    setOutside (
                        TagSet.union outside qvars
                        |> TagSet.union lambdaVarsSet
                    )

                // Set the LambdaOutsideVars set to empty, because variables that occur
                // outside this lambda expression only in other lambda expressions
                // should not be considered nonlocal.
                do! setLambdaOutside TagSet.empty

                let! goal' = quantifyGoal goal

                let! rhsNonLocals = nonLocals

                let rhsNonLocals' =
                    TagSet.difference rhsNonLocals lambdaVarsSet

                do! setQuantVars qvars
                do! setOutside outside
                do! setLambdaOutside lambdaOutside

                // Work out the list of nonlocal curried arguments to the lambda
                // expression. This set must only ever decrease, since the first
                // approximation that make_hlds uses includes all variables in the
                // lambda expression except the quantified variables.
                let lambdaGoalNonLocals = goal'.Info.NonLocals

                let lambdaNonLocals' =
                    List.filter (fun v -> TagSet.contains v lambdaGoalNonLocals) lambdaNonLocals

                return (rhs, rhsNonLocals')
        }

    let implicitlyQuantifyGoal (args: VarId list) (varset: VarSet) (goal: Goal) =
        let info =
            { VarSet = varset
              Seen = emptySetOfVar
              Outside = TagSet.ofList args
              LambdaOutside = emptySetOfVar
              Quantified = emptySetOfVar
              NonLocals = emptySetOfVar }

        let (goal, info') = State.run (quantifyGoal goal) info
        (goal, info'.VarSet)
