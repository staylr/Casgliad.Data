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

    let state = new StateBuilder()

    let setContext (goal: Goal) (modeInfo: ModeInfo) =
        ( (), { modeInfo with CurrentSourceInfo = goal.Info.SourceInfo } )

    let computeGoalInstMapDelta (f: Goal -> ModeStateFunc<GoalExpr>) goal modeInfo =
        let initialInstMap = modeInfo.InstMap
        let (goalExpr, modeInfo') = f goal modeInfo

        let (instMapDelta, modeInfo'') =
            match goal.Goal with
            | Conj([]) ->
                (InstMap.initReachable, { modeInfo' with InstMap = initialInstMap } )
            | _ ->
                (InstMap.computeInstMapDelta initialInstMap modeInfo'.InstMap goal.Info.NonLocals, modeInfo')
        ( { Goal = goalExpr; Info = goal.Info }, modeInfo')

    let rec modecheckGoal goal =
        state {
            do! setContext goal
            return! computeGoalInstMapDelta modecheckGoalExpr goal
        }
    and modecheckGoalExpr goal =
        state {
            return goal.Goal
        }
