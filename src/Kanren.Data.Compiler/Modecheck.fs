namespace Kanren.Data.Compiler

open System.Collections.Generic

open Kanren.Data.Compiler.ModeErrors
open Kanren.Data.Compiler.Delay
open Kanren.Data.Compiler.State

module Modecheck =

    type ModeInfo =
        { PredId: string
          ProcId: int

          VarSet: VarSet
          InstTable: InstTable

          InstMap: InstMap
          DelayInfo: DelayInfo

          Errors: ModeErrorInfo list

          ModeContext: ModeContext

          CurrentSourceInfo: SourceInfo

          // Locked variables, e.g. variables cannot be further instantiated
          // in a negated context.
          LockedVars: SetOfVar

          // Warnings found.
          Warnings: ModeWarningInfo list

          // If rechecking a goal, can calls be made to use a different procedure.
          MayChangeCalledProc: bool

          // Are we checking extra unifications inserted for implied modes.
          // In that case we shouldn't add more such unifications.
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

    let setContext (goal: Goal) (modeInfo: ModeInfo) =
        ( (), { modeInfo with CurrentSourceInfo = goal.Info.SourceInfo } )

    let getInstMap (modeInfo: ModeInfo) =
        ( modeInfo.InstMap, modeInfo )

    let getInstTable (modeInfo: ModeInfo) =
        (modeInfo.InstTable, modeInfo)

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
            elif (not (InstMatch.instMatchesBinding modeInfo.InstTable newInst oldInst (Some varDefn.VarType) InstMatch.AnyMatchesAny)) then
                // TODO
                ((), modeInfo)
            else
                do modeInfo.DelayInfo.bindVar(var)
                ((), { modeInfo with InstMap = modeInfo.InstMap.setVar var newInst })

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
        }

    and modecheckUnify lhs rhs context goalInfo =
        state {
            match rhs with
            | Var (var, varType) -> return! modecheckUnifyVar lhs var varType context goalInfo
        }

    and modecheckUnifyVar lhs rhs rhsType context goalInfo =
        state {
            let! instTable = getInstTable
            let! instMap = getInstMap

            let lhsInst = instMap.lookupVar lhs
            let rhsInst = instMap.lookupVar rhs

            match instTable.unifyInst(lhsInst, rhsInst) with
            | Some (inst, det) ->
                do! setVarInst lhs (Bound inst) (Some lhsInst)
                do! setVarInst rhs (Bound inst) (Some rhsInst)
                return Unify (lhs, (Var (rhs, rhsType)), UnifyMode ((lhsInst, inst), (rhsInst, inst)), context)
            | None ->
                return (raise (System.Exception("TODO")))
        }
