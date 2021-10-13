namespace Kanren.Data.Compiler

open System.Collections.Generic

open Kanren.Data.Compiler.ModeErrors
open Kanren.Data.Compiler.ModeInfo
open Kanren.Data.Compiler.State

module Modecheck =
    let getModeOfArgs (argInitialInsts: InstE list) (finalInst: BoundInstE) =
        let pairWithFinalInst argInitialInsts finalInst =
            argInitialInsts
            |> List.map (fun initInst -> (initInst, finalInst))

        match finalInst with
        | NotReached | Any | Ground ->
            pairWithFinalInst argInitialInsts finalInst
        | BoundCtor boundInsts ->
            match boundInsts.BoundInsts with
            | [] ->
                pairWithFinalInst argInitialInsts NotReached
            | [singleFunctor] ->
                List.map2 (fun i1 i2 -> (i1, i2)) argInitialInsts singleFunctor.ArgInsts
            | _ ->
                failwith "expected single functor in getModeOfArgs"
        | _ ->
            failwith $"unexpected inst in getModeOfArgs {finalInst}"

    let processConj<'T> (f: StateFunc<ModeInfo, 'T>) (modeInfo: ModeInfo) : ('T * DelayedGoal list) * ModeInfo =
        let errors0 = modeInfo.Errors
        let modeInfo' = { modeInfo with Errors = []; DelayInfo = modeInfo.DelayInfo.enterConj() }
        let (res, modeInfo'') = f modeInfo'
        let (delayedGoals, delayInfo') = modeInfo''.DelayInfo.leaveConj()
        ((res, delayedGoals), { modeInfo'' with Errors = List.append errors0 modeInfo''.Errors; DelayInfo = delayInfo' } )

    let rec modecheckGoal goal =
        state {
            do! setContext goal
            return! computeGoalInstMapDelta modecheckGoalExpr goal
        }
    and modecheckGoalExpr goal =
        state {
            match goal.Goal with
            | Unify (lhs, rhs, _, unifyContext) ->
                // set context
                return! modecheckUnify lhs rhs unifyContext goal.Info
            | Conj (goals) ->
                let! goals' = modecheckConjList goals
                return Conj (goals')
            | Disj (goals) ->
                return! modecheckDisjunction goals goal.Info
            | Call (relationId, args) ->
                return! modecheckCall relationId args goal.Info
            | FSharpCall (callee, retVal, args) ->
                return goal.Goal
        }

    and modecheckCall callee args goalInfo =
        state {
            return Call (callee, args)
        }

    and modecheckUnify lhs rhs context goalInfo =
        state {
            match rhs with
            | Var (var, _) -> return! modecheckUnifyVar lhs var context goalInfo
            | Constructor (ctor, args, _, _, _) -> return! modecheckUnifyVarCtor lhs ctor args context goalInfo
            | Lambda _ -> return raise (System.Exception("NYI: modecheckUnify of Lambda"))
        }

    and modecheckUnifyVar lhs rhs context goalInfo =
        state {
            let! instTable = getInstTable
            let! instMap = getInstMap

            let lhsInst = instMap.lookupVar lhs
            let rhsInst = instMap.lookupVar rhs

            match instTable.unifyInst(lhsInst, rhsInst) with
            | Some (inst, det) ->

                do! setVarInst lhs (Bound inst) (Some lhsInst)
                do! setVarInst rhs (Bound inst) (Some rhsInst)

                if (initialFinalInstsIsOutput lhsInst (Bound inst)) then
                    return Unify (lhs, Var (rhs, VarVarUnifyType.Assign), UnifyMode ((lhsInst, inst), (rhsInst, inst)), context)
                elif (initialFinalInstsIsOutput rhsInst (Bound inst)) then
                    return Unify (rhs, Var (lhs, VarVarUnifyType.Assign), UnifyMode ((rhsInst, inst), (lhsInst, inst)), context)
                else
                    return Unify (lhs, Var (rhs, VarVarUnifyType.Test), UnifyMode ((lhsInst, inst), (rhsInst, inst)), context)

            | None ->
                let waitingVars = TagSet.ofList [lhs; rhs]
                let error = ModeErrors.ModeErrorUnifyVarVar (lhs, rhs, lhsInst, rhsInst)
                do! modeError waitingVars error

                // Suppress follow-on errors.
                let unifiedInst = Bound NotReached
                do! setVarInst lhs unifiedInst None
                do! setVarInst rhs unifiedInst None

                return Unify (lhs, Var (rhs, VarVarUnifyType.Test), UnifyMode ((lhsInst, NotReached), (rhsInst, NotReached)), context)
        }

    and modecheckUnifyVarCtor lhs ctor args context goalInfo =
        let createSubUnify (arg: VarId) (var: VarId) (extraGoals: ExtraGoals) =
            let unifyGoalInfo =
                { GoalInfo.init goalInfo.SourceInfo with
                    NonLocals = seq { arg; var } |> TagSet.ofSeq
                }
            let unifyMode = ((Bound NotReached, NotReached), (Bound NotReached, NotReached))
            let goal = { Goal = Unify(arg, Var (var, VarVarUnifyType.Test), unifyMode, context); Info = unifyGoalInfo  }
            extraGoals.AfterGoals.Add(goal)

        let rec splitComplicatedSubUnifies (args0: VarId list) (modes: UnifyMode list) (argsRes: VarId list) (extraGoals: ExtraGoals) =
            state {
                match (args0, modes) with
                | ([], []) ->
                   return List.rev argsRes
                | (arg :: args1, ((li, lf), (ri, rf)) :: modes1) ->
                    // If both sides are input we need to add a test unification.
                    if (li <> Free && ri <> Free) then
                        let! var = cloneVar arg
                        do createSubUnify arg var.Id extraGoals
                        return! splitComplicatedSubUnifies args1 modes1 (var.Id :: argsRes) extraGoals
                    else
                        return! splitComplicatedSubUnifies args1 modes1 (arg :: argsRes) extraGoals
                | _ ->
                    return failwith "length mismatch in splitComplicatedSubUnifies"
            }

        state {
            let! instMap = getInstMap
            let! instTable = getInstTable
            let initialLhsInst = instMap.lookupVar lhs
            let initialArgInsts = List.map instMap.lookupVar args
            let! lvar = lookupVar lhs

            let instDet = instTable.unifyInstFunctor(initialLhsInst, ctor, initialArgInsts, lvar.VarType)
            match instDet with
            | Some (unifiedInst, det) ->
                // TODO Fix Free here. Hopefully will be able to remove unifyMode altogether.
                let unifyMode = ((initialLhsInst, unifiedInst), (Free, unifiedInst))
                let unifyType = if (initialLhsInst = Free) then VarCtorUnifyType.Construct else VarCtorUnifyType.Deconstruct
                let argFromToInsts = getModeOfArgs initialArgInsts unifiedInst
                let initInstOfLhsArgs = instTable.getArgInsts(initialLhsInst, ctor, (List.length argFromToInsts))
                let modeOfLhsArgs = getModeOfArgs initInstOfLhsArgs unifiedInst

                let unifyModes = List.zip modeOfLhsArgs argFromToInsts

                match unifyType with
                | Construct ->
                    do! setVarInst lhs (Bound unifiedInst) (Some Free)

                    return Unify(lhs, Constructor (ctor, args, unifyType, modeOfLhsArgs, Kanren.Data.CannotFail), unifyMode, context)
                | Deconstruct ->
                    let extraGoals = ExtraGoals.init()
                    let! args' = splitComplicatedSubUnifies args unifyModes [] extraGoals
                    let canFail =
                        match instTable.expand(initialLhsInst) with
                        | Bound (BoundCtor { BoundInsts = [_]; TestResults = _ }) ->
                            Kanren.Data.CannotFail
                        | _ ->
                            Kanren.Data.CanFail

                    do! setVarInst lhs (Bound unifiedInst) (Some initialLhsInst)
                    do! bindArgs (Bound unifiedInst) args' initialArgInsts

                    let expr =
                        Unify (lhs, Constructor (ctor, args', unifyType, modeOfLhsArgs, canFail), unifyMode, context)
                    return! handleExtraGoals args args' goalInfo expr instMap extraGoals
            | None ->
                let waitingVars = args |> Seq.ofList |> Seq.append [lhs] |> TagSet.ofSeq
                let error = ModeErrors.ModeErrorUnifyVarFunctor (lhs, ctor, args, initialLhsInst, initialArgInsts)
                do! modeError waitingVars error

                // Suppress follow-on errors.
                let unifiedInst = Bound NotReached
                do! setVarInst lhs unifiedInst None
                do! bindArgs unifiedInst args initialArgInsts

                return Disj([])
        }
    and handleExtraGoals (oldArgs: VarId list) (newArgs: VarId list) (goalInfo0: GoalInfo) (goalExpr: GoalExpr)
                            (initialInstMap: InstMap) (extraGoals: ExtraGoals) =
        state {
            let! haveErrors = haveErrors
            let! checkingExtraGoals = checkingExtraGoals
            if (checkingExtraGoals) then
                failwith "handleExtraGoals called recursively"

            if (haveErrors
                || not (extraGoals.isEmpty ())
                || not (initialInstMap.isReachable ()))
            then
                let oldArgVars = TagSet.ofList oldArgs
                let newArgVars = TagSet.ofList newArgs
                let introducedVars = TagSet.difference newArgVars oldArgVars
                let nonLocals = (TagSet.union goalInfo0.NonLocals introducedVars) |> TagSet.intersect newArgVars
                let goalInfo = { goalInfo0 with NonLocals = nonLocals }
                let goalList = List.append (List.ofSeq extraGoals.BeforeGoals)
                                   ({ Goal = goalExpr; Info = goalInfo } :: List.ofSeq extraGoals.AfterGoals)
                let goalArray = ResizeArray<Goal>()
                let! _ = withNoDelayOrExtraGoals (modecheckConjListNoDelay goalList goalArray)
                return Conj (List.ofSeq goalArray)
            else
                return goalExpr
        }

    and modecheckConjListNoDelay goals goalArray =
        state {
            match goals with
            | [] ->
                return ()
            | goal :: goals' ->
                let! goal' = modecheckGoal goal
                let! instMap = getInstMap
                if (instMap.isReachable ()) then
                    do goalArray.Add(goal')
                    return! modecheckConjListNoDelay goals' goalArray
                else
                    do goalArray.Add(goal)
                    return ()
        }

    and modecheckConjList (goals: Goal list) =
        state {
            let scheduledGoals = ResizeArray<Goal>()
            let! (_, delayedGoals) = processConj (modecheckConjListFlattenAndSchedule goals scheduledGoals)

            let scheduledDelayedGoals = ResizeArray<Goal>()
            let! delayedGoals' = modecheckDelayedGoals delayedGoals scheduledDelayedGoals
            do scheduledGoals.AddRange(scheduledDelayedGoals)
            match delayedGoals' with
            | [] ->
                ()
            | [delayedGoal] ->
                do! modeErrorWithInfo delayedGoal.ErrorInfo
            | _ :: _ ->
                let error = ModeErrorUnschedulableConjuncts delayedGoals
                let waitingVars = delayedGoals |> List.fold (fun vs g -> TagSet.union vs g.Vars) TagSet.empty
                do! modeError waitingVars error

            return Seq.append scheduledGoals scheduledDelayedGoals |> List.ofSeq
        }

    and modecheckConjListFlattenAndSchedule goals scheduledGoals : StateFunc<ModeInfo, unit> =
        state {
            match goals with
            | [] ->
                return ()
            | goal :: goals' ->
                match goal.Goal with
                | Conj(subGoals) ->
                    return! modecheckConjListFlattenAndSchedule
                            (List.append subGoals goals') scheduledGoals
                | _ ->
                    let! instMap0 = getInstMap
                    let! delayInfo0 = getDelayInfo

                    let! goal' = modecheckGoal goal
                    let! goalErrors = getErrors
                    match goalErrors with
                    | [] ->
                        match goal'.Goal with
                        | Conj(subGoals) ->
                            do scheduledGoals.AddRange(subGoals)
                        | _ ->
                            do scheduledGoals.Add(goal')
                    | firstError :: _ ->
                        do! delayConjunct firstError goal instMap0 delayInfo0

                    let! wokenGoals = wakeupGoals
                    let goals'' = List.append wokenGoals goals'

                    let! instMap = getInstMap
                    if (instMap.isReachable()) then
                        return! modecheckConjListFlattenAndSchedule goals'' scheduledGoals
                    else
                        // We should not mode-analyse the remaining goals, since they are
                        // unreachable. Instead we optimize them away, so that later passes
                        // won't complain about them not having mode information.
                        return ()
        }

    and modecheckDelayedGoals delayedGoals (goals: ResizeArray<Goal>) =
        state {
            match delayedGoals with
            | [] ->
                return []
            | _ :: _ ->
                let goalsToProcess = delayedGoals |> List.map (fun dg -> dg.Goal)
                let scheduledGoals = ResizeArray<Goal>()
                let! (_, delayedGoals') = processConj (modecheckConjListFlattenAndSchedule goalsToProcess scheduledGoals)
                if (List.length delayedGoals') < (List.length delayedGoals) then
                    // We scheduled some goals. Keep going until we either
                    // flounder or succeed.
                    return! modecheckDelayedGoals delayedGoals' goals
                else
                    return delayedGoals'
        }

    and modecheckDisjunction goals goalInfo =
        state {
            match goals with
            | [] ->
                do! setInstMap InstMap.initUnreachable
                return Disj([])
            | _ :: _ ->
                let! instMap0 = getInstMap
                let! (goals', armInstMaps) = modecheckDisjuncts instMap0 goals
                do! setInstMap instMap0
                do! instMapMerge goalInfo.NonLocals armInstMaps MergeContext.MergeDisjunction
                return Simplify.flattenDisjunction goals'
        }

    and modecheckDisjuncts instMap0 goals =
        state {
            match goals with
            | [] ->
                return ([], [])
            | goal :: goals' ->
                do! setInstMap instMap0
                let! goal' = modecheckGoal goal
                let! armInstMap = getInstMap
                let! (goals'', armInstMaps) = modecheckDisjuncts instMap0 goals'
                return (goal' :: goals'', (goal'.Info.SourceInfo, armInstMap) :: armInstMaps)
        }

    let modecheckBodyGoal predId procId varset args argModes instTable lookupRelationModes lookupFunctionModes (goal: Goal) =
        let instMap = List.fold2 (fun (instMap': InstMap) arg (initialInst, _) -> instMap'.setVar arg initialInst)
                            InstMap.initReachable args argModes

        let modeInfo = ModeInfo.init predId procId ModeContext.ModeContextUninitialized
                            goal.Info.SourceInfo varset instTable instMap true
                            lookupRelationModes lookupFunctionModes
        let (goal', modeInfo') = State.run (modecheckGoal goal) modeInfo
        (goal', modeInfo'.Errors, modeInfo'.InstMap, modeInfo'.VarSet)
