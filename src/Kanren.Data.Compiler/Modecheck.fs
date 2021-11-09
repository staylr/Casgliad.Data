namespace Kanren.Data.Compiler

open Kanren.Data.Compiler.ModeErrors
open Kanren.Data.Compiler.ModeInfo
open Kanren.Data.Compiler.State

module internal Modecheck =
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
                invalidOp "expected single functor in getModeOfArgs"
        | _ ->
            invalidOp $"unexpected inst in getModeOfArgs {finalInst}"

    let processConj<'T> (f: StateFunc<ModeInfo, 'T>) (modeInfo: ModeInfo) : ('T * DelayedGoal list) * ModeInfo =
        let errors0 = modeInfo.Errors
        let modeInfo' = { modeInfo with Errors = []; DelayInfo = modeInfo.DelayInfo.enterConj() }
        let (res, modeInfo'') = f modeInfo'
        let (delayedGoals, delayInfo') = modeInfo''.DelayInfo.leaveConj()
        ((res, delayedGoals), { modeInfo'' with Errors = List.append errors0 modeInfo''.Errors; DelayInfo = delayInfo' } )

    let createVarVarUnify (arg: VarId) (var: VarId) modeContext (sourceInfo: SourceInfo) : Goal =
        let unifyGoalInfo =
            { GoalInfo.init sourceInfo with
                NonLocals = seq { arg; var } |> TagSet.ofSeq
            }
        let unifyMode = ((Bound NotReached, NotReached), (Bound NotReached, NotReached))
        let unifyContext = unifyContextOfModeContext modeContext
        { Goal = Unify (arg, Var (var, VarVarUnifyType.Test), unifyMode, unifyContext)
          Info = unifyGoalInfo }

    let handleImpliedMode var (varInst0: InstE) (initialInst0: InstE) (extraGoals: ExtraGoals) =
        state {
            let! instTable = getInstTable
            let varInst = instTable.expand(varInst0)
            let initialInst = instTable.expand(initialInst0)
            let! varDefn = lookupVar var

            // If the initial inst of the variable matches_final the initial inst
            // specified in the relation's mode declaration, then it is not a call
            // to an implied mode, it is an exact match with a genuine mode.
            if (InstMatch.instMatchesFinal instTable varInst initialInst (Some varDefn.VarType)) then
                return var
            elif (initialInst = Bound Any && varInst = Free) then
                invalidOp "Any implied insts not yet implemented"
                return var
            else
                let! var' = cloneVar var
                let! modeContext = getModeContext
                let! sourceInfo = getContext
                let unifyGoal = createVarVarUnify var'.Id var modeContext sourceInfo
                extraGoals.AfterGoals.Add(unifyGoal)
                return var'.Id
        }

    let setVarInstCall var initialInst finalInst (extraGoals: ExtraGoals) =
        state {
            let! instMap = getInstMap
            if (instMap.isReachable()) then
                let varInst = instMap.lookupVar var
                let! var' = handleImpliedMode var varInst initialInst extraGoals
                do! setVarInst var (Bound finalInst) None
                if (var <> var') then
                    do! setVarInst var' (Bound finalInst) None

                return var'
            else
                return var
        }

    let rec setVarInstListCall argNum vars initialInsts finalInsts (extraGoals: ExtraGoals) =
        state {
            match (vars, initialInsts, finalInsts) with
            | ([], [], []) ->
                return []
            | (var :: vars', initialInst :: initialInsts', finalInst :: finalInsts') ->
                do! setCallArgContext argNum
                let! var' = setVarInstCall var initialInst finalInst extraGoals
                let! vars'' = setVarInstListCall (argNum + 1) vars' initialInsts' finalInsts' extraGoals
                return var' :: vars''
            | _ ->
                return invalidOp "setVarInstListCall"
        }

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
            | Conjunction (goals) ->
                let! goals' = modecheckConjList goals
                return Conjunction (goals')
            | Disjunction (goals) ->
                return! modecheckDisjunction goals goal.Info
            | Call (relationId, args) ->
                return! modecheckCall relationId args goal.Info
            | FSharpCall (callee, retVal, args) ->
                return! modecheckFSharpCall callee retVal args goal.Info
            | IfThenElse (condGoal, thenGoal, elseGoal) ->
                return! modecheckIfThenElse condGoal thenGoal elseGoal goal.Info
            | Not (negGoal) ->
                return! modecheckNegation negGoal goal.Info
            | Switch (_, _, _) ->
                return goal.Goal
        }

    and modecheckNegation negGoal goalInfo =
        state {
            let! instMap0 = getInstMap
            // TODO: disallow any non-locals with inst Any - further constraining
            // variables within a negation is not allowed.
            let! negGoal' = withLockedVars VarLockReason.VarLockNegation goalInfo.NonLocals
                               (modecheckGoal negGoal)
            do! setInstMap instMap0
            return Not (negGoal')
        }

    and modecheckIfThenElse condGoal thenGoal elseGoal goalInfo =
        state {
            let! instMap0 = getInstMap
            let! condGoal' = withLockedVars VarLockReason.VarLockIfThenElse goalInfo.NonLocals
                                            (modecheckGoal condGoal)
            let! condInstMap = getInstMap
            let! (thenGoal', thenInstMap) =
                if (condInstMap.isReachable()) then
                    state {
                        let! thenGoal'' = modecheckGoal thenGoal
                        let! thenInstMap' = getInstMap
                        return (thenGoal'', thenInstMap')
                    }
                else
                    state {
                        return (succeedGoal, condInstMap)
                    }

            do! setInstMap instMap0
            let! elseGoal' = modecheckGoal elseGoal
            let! elseInstMap = getInstMap

            let armInstMaps = [ (thenGoal.Info.SourceInfo, thenInstMap); (elseGoal.Info.SourceInfo, elseInstMap) ]
            do! instMapMerge goalInfo.NonLocals armInstMaps MergeContext.MergeIfThenElse
            return IfThenElse (condGoal', thenGoal', elseGoal')
        }

    and modecheckCall callee args goalInfo =
        state {
            let! instMap0 = getInstMap
            let! modes = getCalledRelationModeInfo callee
            do! setCallContext (RelationCallee (fst callee))
            match modes with
            | [] ->
                return invalidOp "unexpected - no modes in modecheckCall"
            | [singleMode] ->
                let initialInsts = (List.map fst singleMode.Modes.Modes)
                let finalInsts = (List.map snd singleMode.Modes.Modes)
                do! varHasInstListNoExactMatch args initialInsts
                let buildCall = (fun a -> Call ((fst callee, singleMode.ProcId), a))
                return! modecheckEndOfCall buildCall args initialInsts finalInsts
                            singleMode.ProcId singleMode.Modes.Determinism instMap0 goalInfo
            | _ :: _ ->
                 // TODO
                 return invalidOp "not implemented - relations with multiple modes"
        }

    and modecheckFSharpCall callee ret args goalInfo =
        state {
            let! instMap0 = getInstMap
            let! modes = getCalledFunctionModeInfo callee
            do! setCallContext (FSharpCallee (fst callee))
            match modes with
            | [] ->
                return invalidOp "unexpected - no modes in modecheckCall"
            | [singleMode] ->
                let (allArgs, allModes) =
                    match ret with
                    | Some (retArg) ->
                        (List.append args [retArg], List.append singleMode.Modes.Modes [singleMode.ResultMode])
                    | None ->
                        (args, singleMode.Modes.Modes)

                let initialInsts = List.map fst allModes
                let finalInsts = List.map snd allModes
                do! varHasInstListNoExactMatch allArgs initialInsts
                let buildCall a =
                    match ret with
                    | Some _ ->
                        FSharpCall ((fst callee, singleMode.ProcId), Some (List.head a), List.tail a)
                    | None ->
                        FSharpCall ((fst callee, singleMode.ProcId), None, a)

                return! modecheckEndOfCall buildCall allArgs initialInsts finalInsts
                            singleMode.ProcId singleMode.Modes.Determinism instMap0 goalInfo
            | _ :: _ ->
                 // TODO
                 return invalidOp "not implemented - relations with multiple modes"
        }

    and modecheckEndOfCall buildCall args initialInsts finalInsts procId det instMap0 goalInfo =
        state {
            let extraGoals = ExtraGoals.init()
            let! args' = setVarInstListCall 1 args initialInsts finalInsts extraGoals
            let (maxSoln, _) = determinismComponents det
            if (maxSoln = Kanren.Data.NumSolutions.NoSolutions) then
                do! setInstMap (InstMap.initUnreachable)

            let call = buildCall args'
            let! goal = handleExtraGoals args args' goalInfo call instMap0 extraGoals
            do! unsetCallContext
            return goal
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
                let error = ModeErrorUnifyVarVar (lhs, rhs, lhsInst, rhsInst)
                do! modeError waitingVars error

                // Suppress follow-on errors.
                let unifiedInst = Bound NotReached
                do! setVarInst lhs unifiedInst None
                do! setVarInst rhs unifiedInst None

                return Unify (lhs, Var (rhs, VarVarUnifyType.Test), UnifyMode ((lhsInst, NotReached), (rhsInst, NotReached)), context)
        }

    and modecheckUnifyVarCtor lhs ctor args context goalInfo =
        let rec splitComplicatedSubUnifies (args0: VarId list) (modes: UnifyMode list) (argsRes: VarId list) (extraGoals: ExtraGoals) =
            state {
                match (args0, modes) with
                | ([], []) ->
                   return List.rev argsRes
                | (arg :: args1, ((li, lf), (ri, rf)) :: modes1) ->
                    // If both sides are input we need to add a test unification.
                    if (li <> Free && ri <> Free) then
                        let! var = cloneVar arg
                        let unifyGoal = createVarVarUnify arg var.Id (ModeContextUnify context) goalInfo.SourceInfo
                        do extraGoals.AfterGoals.Add(unifyGoal)
                        return! splitComplicatedSubUnifies args1 modes1 (var.Id :: argsRes) extraGoals
                    else
                        return! splitComplicatedSubUnifies args1 modes1 (arg :: argsRes) extraGoals
                | _ ->
                    return invalidOp "length mismatch in splitComplicatedSubUnifies"
            }

        state {
            let! instMap = getInstMap
            let! instTable = getInstTable
            let initialLhsInst = instMap.lookupVar lhs
            let initialArgInsts = List.map instMap.lookupVar args
            let! lhsVar = lookupVar lhs

            let instDet = instTable.unifyInstFunctor(initialLhsInst, ctor, initialArgInsts, lhsVar.VarType)
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
                let error = ModeErrorUnifyVarFunctor (lhs, ctor, args, initialLhsInst, initialArgInsts)
                do! modeError waitingVars error

                // Suppress follow-on errors.
                let unifiedInst = Bound NotReached
                do! setVarInst lhs unifiedInst None
                do! bindArgs unifiedInst args initialArgInsts

                return Disjunction([])
        }
    and handleExtraGoals (oldArgs: VarId list) (newArgs: VarId list) (goalInfo0: GoalInfo) (goalExpr: GoalExpr)
                            (initialInstMap: InstMap) (extraGoals: ExtraGoals) : ModeStateFunc<GoalExpr> =
        state {
            let! haveErrors = haveErrors
            let! checkingExtraGoals = checkingExtraGoals

            if (not haveErrors
                && not (extraGoals.isEmpty ())
                && not (initialInstMap.isReachable ()))
            then
                if (checkingExtraGoals) then
                    invalidOp "handleExtraGoals called recursively"

                let oldArgVars = TagSet.ofList oldArgs
                let newArgVars = TagSet.ofList newArgs
                let introducedVars = TagSet.difference newArgVars oldArgVars
                let nonLocals =
                        TagSet.union goalInfo0.NonLocals introducedVars
                        |> TagSet.intersect newArgVars
                let goalInfo = { goalInfo0 with NonLocals = nonLocals }
                let goalList = List.append (List.ofSeq extraGoals.BeforeGoals)
                                   ({ Goal = goalExpr; Info = goalInfo } :: List.ofSeq extraGoals.AfterGoals)
                let goalArray = ResizeArray<Goal>()
                let! _ = withNoDelayOrExtraGoals (modecheckConjListNoDelay goalList goalArray)
                return Conjunction (List.ofSeq goalArray)
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
                | Conjunction(subGoals) ->
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
                        | Conjunction(subGoals) ->
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
                return Disjunction([])
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
        let (goal', modeInfo') = run (modecheckGoal goal) modeInfo
        (goal', modeInfo'.Errors, modeInfo'.InstMap, modeInfo'.VarSet)
