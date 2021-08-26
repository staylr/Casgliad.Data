namespace Kanren.Data.Compiler

open System.Collections.Generic

open Kanren.Data.Compiler.ModeErrors

module Delay =
    [<Measure>]
    type private depthNumMeasure

    [<Measure>]
    type private seqNumMeasure

    type private DepthNum = int<depthNumMeasure>
    type private SeqNum = int<seqNumMeasure>
    type private DelayGoalNum = { DepthNum: DepthNum; SeqNum: SeqNum }

    // A delay_goal_stack has one entry for each conjunction depth,
    // the current depth being at the top. The entry for the conjunction
    // at each depth maps the seq_num of each conjunct to the delayed_goal
    // construct of that goal.
    type private DelayConjInfo =
        { DelayedGoals: ResizeArray<DelayedGoal option>
          mutable NextSeqNum: SeqNum }

    type private WaitingGoals = Dictionary<DelayGoalNum, SetOfVar>

    type private WaitingGoalsTable = Dictionary<VarId, WaitingGoals>

    type private PendingGoalsTable = Dictionary<DepthNum, ResizeArray<SeqNum>>

    type DelayInfo =
        private
            { mutable CurrentDepth: DepthNum
              DelayedGoalStack: Stack<DelayConjInfo>
              WaitingGoals: WaitingGoalsTable
              PendingGoals: PendingGoalsTable }
        static member init() =
            { CurrentDepth = 0<depthNumMeasure>
              DelayedGoalStack = Stack<DelayConjInfo> ()
              WaitingGoals = WaitingGoalsTable ()
              PendingGoals = PendingGoalsTable () }

        member this.enterConj() =
            let conjInfo =
                { DelayedGoals = ResizeArray<DelayedGoal option> ()
                  NextSeqNum = 0<seqNumMeasure> }

            do this.DelayedGoalStack.Push (conjInfo)
            this.CurrentDepth <- this.CurrentDepth + 1<depthNumMeasure>

        member this.leaveConj delayedGoalsList =
            let currentDepth = this.CurrentDepth
            let delayedGoals = this.DelayedGoalStack.Pop ()

            let flounderedGoals =
                delayedGoals.DelayedGoals
                |> Seq.filter Option.isSome
                |> Seq.map Option.get
                |> List.ofSeq

            // When a conjunction flounders, we need to remove the delayed sub-goals
            // from the waiting goals table before we delay the conjunction as a whole.
            delayedGoals.DelayedGoals
            |> Seq.iteri
                (fun i delayedGoal ->
                    match (delayedGoal) with
                    | Some (delayedGoal) ->
                        let goalNum =
                            { DepthNum = currentDepth
                              SeqNum = i * 1<seqNumMeasure> }

                        this.deleteWaitingVars goalNum delayedGoal.Vars
                    | None -> ())

            do this.CurrentDepth <- this.CurrentDepth - 1<depthNumMeasure>

            flounderedGoals

        member this.delayGoal (error: ModeErrorInfo) (goal: DelayedGoal) =
            let delayedGoals = this.DelayedGoalStack.Peek ()
            delayedGoals.DelayedGoals.Add (Some goal)

            let goalNum =
                { DepthNum = this.CurrentDepth
                  SeqNum = delayedGoals.NextSeqNum }

            do delayedGoals.NextSeqNum <- delayedGoals.NextSeqNum + 1<seqNumMeasure>

            let addWaitingVar var =
                let waitingGoals =
                    match this.WaitingGoals.TryGetValue (var) with
                    | true, waitingGoals -> waitingGoals
                    | _ ->
                        let goals = WaitingGoals ()
                        do this.WaitingGoals.[var] <- goals
                        goals

                waitingGoals.[goalNum] <- error.Vars

            error.Vars |> TagSet.iter addWaitingVar

        member private this.addPendingGoal goalNum waitingVars =
            this.deleteWaitingVars goalNum waitingVars

            let pendingSeqNums =
                match this.PendingGoals.TryGetValue goalNum.DepthNum with
                | true, pendingSeq -> pendingSeq
                | _ ->
                    let pendingSeq = ResizeArray<SeqNum> ()
                    this.PendingGoals.[goalNum.DepthNum] <- pendingSeq
                    pendingSeq

            pendingSeqNums.Add (goalNum.SeqNum)

        member this.bindAllVars() =
            this.WaitingGoals
            |> Seq.iter (fun g -> this.bindVar g.Key)

        member this.bindVar var =
            match this.WaitingGoals.TryGetValue (var) with
            | true, waitingGoals ->
                waitingGoals
                |> Seq.iter (fun g -> this.addPendingGoal g.Key g.Value)
            | _ -> ()

        // Remove all references to a goal from the waiting goals table.
        member private this.deleteWaitingVars goalNum (vars: SetOfVar) =
            vars
            |> TagSet.iter
                (fun var ->
                    let waitingGoals = this.WaitingGoals.[var]
                    waitingGoals.Remove (goalNum) |> ignore

                    if (waitingGoals.Count = 0) then
                        this.WaitingGoals.Remove (var) |> ignore)

        member this.wakeupGoals() =
            match this.PendingGoals.TryGetValue this.CurrentDepth with
            | true, pendingGoals ->
                let conjInfo = this.DelayedGoalStack.Peek ()

                let goals =
                    pendingGoals
                    |> Seq.map
                        (fun s ->
                            let goal = conjInfo.DelayedGoals.[int s]
                            conjInfo.DelayedGoals.[int s] <- None
                            goal.Value.Goal)
                    |> List.ofSeq

                pendingGoals.Clear ()
                goals
            | _ -> []
