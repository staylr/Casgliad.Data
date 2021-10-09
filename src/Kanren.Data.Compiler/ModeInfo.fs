namespace Kanren.Data.Compiler

open Kanren.Data.Compiler.ModeErrors
open Kanren.Data.Compiler.Delay
open Kanren.Data.Compiler.State

module ModeInfo =

    type RelationModeInfo =
        { ProcId: ProcId
          Modes: RelationModeE
          // TODO statistics
        }

    //type LookupRelationModes =

    type ModeInfo =
        { PredId: string
          ProcId: int

          VarSet: VarSet
          InstTable: InstTable

          InstMap: InstMap
          DelayInfo: DelayInfo

          ModeContext: ModeContext

          CurrentSourceInfo: SourceInfo

          // Locked variables, e.g. variables cannot be further instantiated
          // in a negated context.
          LockedVars: SetOfVar

          Errors: ModeErrorInfo list

          Warnings: ModeWarningInfo list

          // If rechecking a goal, can calls be made to use a different procedure.
          MayChangeCalledProc: bool

          // Are we checking extra unifications inserted for implied modes.
          // In that case we shouldn't add more such unifications to avoid
          // infinite recursion.
          CheckingExtraGoals: bool

          // Do we need to rerun quantification.
          NeedToRequantify: bool
        }
        with
        static member init predId procId modeContext currentSourceInfo varset instTable instmap mayChangeProc =
                            { PredId = predId
                              ProcId = procId
                              InstMap = instmap
                              VarSet = varset
                              DelayInfo = DelayInfo.init ()
                              Errors = []
                              Warnings = []
                              InstTable = instTable
                              ModeContext = modeContext
                              CurrentSourceInfo = currentSourceInfo
                              LockedVars = emptySetOfVar
                              MayChangeCalledProc = mayChangeProc
                              CheckingExtraGoals = false
                              NeedToRequantify = false
                            }

    type ModeStateFunc<'T> = StateFunc<ModeInfo, 'T>

    let state = StateBuilder()

    type ExtraGoals = { BeforeGoals : ResizeArray<Goal>; AfterGoals: ResizeArray<Goal> }
        with
        static member init () = { BeforeGoals = ResizeArray<Goal>(); AfterGoals = ResizeArray<Goal>() }

        member x.isEmpty () = x.BeforeGoals.Count = 0 && x.AfterGoals.Count = 0

    let setContext (goal: Goal) (modeInfo: ModeInfo) =
        ( (), { modeInfo with CurrentSourceInfo = goal.Info.SourceInfo } )


    let haveErrors (modeInfo: ModeInfo) =
        ( modeInfo.Errors <> [], modeInfo )

    let clearErrors (modeInfo: ModeInfo) =
        ( (), { modeInfo with Errors = [] })

    let getErrors (modeInfo: ModeInfo) =
        ( modeInfo.Errors, modeInfo )

    let getInstMap (modeInfo: ModeInfo) =
        ( modeInfo.InstMap, modeInfo )

    let getDelayInfo (modeInfo: ModeInfo) =
        ( modeInfo.DelayInfo, modeInfo )

    let setInstMap instMap (modeInfo: ModeInfo) =
        ( (), { modeInfo with InstMap = instMap } )

    let lookupVar v (modeInfo: ModeInfo) =
        ( modeInfo.VarSet.Vars.[v], modeInfo )

    let cloneVar v (modeInfo: ModeInfo) =
        let var = modeInfo.VarSet.Vars.[v]
        let (varset, newVar) = modeInfo.VarSet.newNamedVar(var.Name, var.VarType)
        ( newVar, { modeInfo with VarSet = varset })

    let getInstTable (modeInfo: ModeInfo) =
        (modeInfo.InstTable, modeInfo)

    let varIsLocked (modeInfo: ModeInfo) var = false

    let modeError waitingVars error (modeInfo: ModeInfo) =
        let errorInfo = { ModeErrorInfo.Vars = waitingVars; Error = error; SourceInfo = modeInfo.CurrentSourceInfo; ModeContext = modeInfo.ModeContext  }
        ((), { modeInfo with Errors = List.append (modeInfo.Errors) [errorInfo] })

    let modeErrorWithInfo errorInfo (modeInfo: ModeInfo) =
        ((), { modeInfo with Errors = List.append (modeInfo.Errors) [errorInfo] })

    let setVarInst (var: VarId) (newInst0: InstE) (maybeUnifiedInst: InstE option) modeInfo =
        if not (modeInfo.InstMap.isReachable()) then
            ((), modeInfo)
        else
            let oldInst = modeInfo.InstMap.lookupVar var
            let newInst =
                if (oldInst = newInst0) then
                    newInst0
                else
                    match (modeInfo.InstTable.unifyInst(oldInst, newInst0)) with
                    | Some (unifiedInst, _) -> Bound unifiedInst
                    | None -> failwith "unexpected: unify_inst failed"
            let varDefn = modeInfo.VarSet.Vars.[var]
            if (Bound NotReached = (modeInfo.InstTable.expand(newInst))) then
                // If the top-level inst of the variable is NotReached then the
                // instmap as a whole must be unreachable.
                ((), { modeInfo with InstMap = InstMap.initUnreachable })
            elif (InstMatch.instMatchesInitial modeInfo.InstTable oldInst newInst (Some varDefn.VarType)) then
                // No added information or binding.
                // TODO - can this actually happen? It can in Mercury when uniqueness is lost.
                ((), { modeInfo with InstMap = modeInfo.InstMap.setVar var newInst })
            elif (not (InstMatch.instMatchesBinding modeInfo.InstTable newInst oldInst (Some varDefn.VarType) InstMatch.AnyMatchesAny)
                  && varIsLocked modeInfo var ) then
                // TODO
                ((), modeInfo)
            else
                let delayInfo = modeInfo.DelayInfo.bindVar(var)
                ((), { modeInfo with InstMap = modeInfo.InstMap.setVar var newInst; DelayInfo = delayInfo })

    let bindArgs inst argVars unifyArgInsts =
        state {
            if (inst = Bound NotReached) then
                do! setInstMap InstMap.initUnreachable
            else
                let argsAndInsts = List.zip argVars unifyArgInsts
                match inst with
                | Bound Ground ->
                    for (arg, argInst) in argsAndInsts do
                        do! setVarInst arg (Bound Ground) (Some argInst)
                | Bound (BoundCtor details) ->
                    match details.BoundInsts with
                    | [] ->
                        do! setInstMap InstMap.initUnreachable
                    | [boundInst] ->
                        let boundArgsAndInsts = List.zip3 argVars boundInst.ArgInsts unifyArgInsts
                        for (arg, boundArgInst, argInst) in boundArgsAndInsts do
                            do! setVarInst arg (Bound boundArgInst) (Some argInst)
                    | _ :: _ ->
                        failwith "Expected single constructor in bindArgs"
        }

    // Given a list of insts of a given variable that reflect the inst of that
    // variable at the ends of a branched control structure such as a
    // disjunction or if-then-else, return either `Some(MergedInst)' where
    // MergedInst is the final inst of that variable after the branched control
    // structure as a whole, or `None' if some of the insts are not compatible.
    let rec mergeVarInsts (instTable: InstTable) insts varType =
        match insts with
        | [] ->
            failwith "mergeVarInsts: empty list"
        | [inst] ->
            Some inst
        | [inst1; inst2] ->
            instTable.mergeInst(inst1, inst2, varType)
        | _ ->
            let (list1, list2) = List.splitAt ((List.length insts) / 2) insts
            let merged1 = mergeVarInsts instTable list1 varType
            let merged2 = mergeVarInsts instTable list2 varType
            match (merged1, merged2) with
            | (Some mergedInst1, Some mergedInst2) ->
                instTable.mergeInst(mergedInst1, mergedInst2, varType)
            | _ ->
                None

    // Merge the InstMaps at the end of each branch of a branched control structure.
    let instMapMerge nonLocals (armInstMaps: (SourceInfo * InstMap) list) mergeContext modeInfo =
        let mergeInstOfVar (instMap: InstMap, errors) var =
            let varInsts = armInstMaps |> List.map (fun (_, armInstMap) -> armInstMap.lookupVar var )
            let varDefn = modeInfo.VarSet.Vars.[var]
            let maybeMergedInst = mergeVarInsts modeInfo.InstTable varInsts (Some varDefn.VarType)
            match maybeMergedInst with
            | Some mergedInst ->
                let contexts = armInstMaps |> List.map fst
                let contextInsts = List.zip contexts varInsts
                let mergeError = { MergeError.Var = var; Insts = contextInsts }
                (instMap.setVar var mergedInst, mergeError :: errors)
            | None ->
                (instMap.setVar var (Bound NotReached), errors)

        let instMap0 = modeInfo.InstMap
        let reachableInstMaps = armInstMaps |> List.filter (fun (_, instMap) -> instMap.isReachable())
        if (instMap0.isReachable() && reachableInstMaps <> []) then
            let (instMap, mergeErrors) = nonLocals |> TagSet.fold mergeInstOfVar (instMap0, [])
            let (_, modeInfo') = setInstMap instMap modeInfo
            match mergeErrors with
            | [] ->
                ((), modeInfo')
            | firstError :: _ ->
                let error = ModeErrorMergeDisjunction (mergeContext, mergeErrors)
                modeError (seq { firstError.Var } |> TagSet.ofSeq) error modeInfo'
        else
            setInstMap InstMap.initUnreachable modeInfo

    let computeGoalInstMapDelta (f: Goal -> ModeStateFunc<GoalExpr>) goal modeInfo =
        let initialInstMap = modeInfo.InstMap
        let (goalExpr, modeInfo') = f goal modeInfo

        let (instMapDelta, modeInfo'') =
            match goal.Goal with
            | Conj([]) ->
                (InstMap.initReachable, { modeInfo' with InstMap = initialInstMap } )
            | _ ->
                (InstMap.computeInstMapDelta initialInstMap modeInfo'.InstMap goal.Info.NonLocals, modeInfo')
        ( { Goal = goalExpr; Info = { goal.Info with InstMapDelta = instMapDelta } }, modeInfo'')

    let delayConjunct firstError goal instMap0 (delayInfo0: DelayInfo) (modeInfo: ModeInfo) : unit * ModeInfo =
        let delayInfo = delayInfo0.delayGoal firstError goal
        ((), { modeInfo with InstMap = instMap0; DelayInfo = delayInfo; Errors = [] })

    let wakeupGoals (modeInfo: ModeInfo) =
        let (wokenGoals, delayInfo) = modeInfo.DelayInfo.wakeupGoals()
        (wokenGoals, { modeInfo with DelayInfo = delayInfo })

    let withNoDelayOrExtraGoals f modeInfo =
        let mayChangeCalledProc = modeInfo.MayChangeCalledProc
        let modeInfo' = { modeInfo with MayChangeCalledProc = false; CheckingExtraGoals = true }
        let (res, modeInfo'') = f modeInfo
        (res, { modeInfo with MayChangeCalledProc = mayChangeCalledProc; CheckingExtraGoals = false })

    let checkingExtraGoals modeInfo = (modeInfo.CheckingExtraGoals, modeInfo)
