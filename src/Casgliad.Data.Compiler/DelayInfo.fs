namespace Casgliad.Data.Compiler

open System.Collections.Immutable

open Casgliad.Data.Compiler.ModeErrors

module internal Delay =
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
        { DelayedGoals: ImmutableDictionary<SeqNum, DelayedGoal>
          NextSeqNum: SeqNum }

    type private WaitingGoals = ImmutableDictionary<DelayGoalNum, SetOfVar>

    type private WaitingGoalsTable = ImmutableDictionary<VarId, WaitingGoals>

    type private PendingGoalsTable = ImmutableDictionary<DepthNum, ImmutableList<SeqNum>>

    type DelayInfo =
        private
            { CurrentDepth: DepthNum
              DelayedGoalStack: ImmutableStack<DelayConjInfo>
              WaitingGoals: WaitingGoalsTable
              PendingGoals: PendingGoalsTable }
        static member init() =
            { CurrentDepth = 0<depthNumMeasure>
              DelayedGoalStack = ImmutableStack.Create<DelayConjInfo> ()
              WaitingGoals = WaitingGoalsTable.Empty
              PendingGoals = PendingGoalsTable.Empty }

        member this.enterConj() =
            let conjInfo =
                { DelayedGoals = ImmutableDictionary.Empty
                  NextSeqNum = 0<seqNumMeasure> }

            { this with
                  DelayedGoalStack = this.DelayedGoalStack.Push (conjInfo)
                  CurrentDepth = this.CurrentDepth + 1<depthNumMeasure> }

        member this.leaveConj() =
            let currentDepth = this.CurrentDepth
            let delayedGoals = this.DelayedGoalStack.Peek ()
            let delayedGoalStack = this.DelayedGoalStack.Pop ()

            let flounderedGoals =
                delayedGoals.DelayedGoals
                |> Seq.map (fun x -> x.Value)
                |> List.ofSeq

            // When a conjunction flounders, we need to remove the delayed sub-goals
            // from the waiting goals table before we delay the conjunction as a whole.

            let this' =
                delayedGoals.DelayedGoals
                |> Seq.fold
                    (fun (s: DelayInfo) delayedGoal ->
                        let goalNum =
                            { DepthNum = currentDepth
                              SeqNum = delayedGoal.Key }

                        s.deleteWaitingVars goalNum delayedGoal.Value.Vars)
                    this

            (flounderedGoals,
             { this' with
                   DelayedGoalStack = delayedGoalStack
                   CurrentDepth = currentDepth - 1<depthNumMeasure> })

        member this.delayGoal (error: ModeErrorInfo) (goal: Goal) =
            let delayConjInfo = this.DelayedGoalStack.Peek ()
            let nextSeqNum = delayConjInfo.NextSeqNum

            let delayedGoal =
                { DelayedGoal.Goal = goal
                  Vars = error.Vars
                  ErrorInfo = error }

            let delayedGoals' =
                delayConjInfo.DelayedGoals.Add (delayConjInfo.NextSeqNum, delayedGoal)

            let delayConjInfo' =
                { delayConjInfo with
                      NextSeqNum = delayConjInfo.NextSeqNum + 1<seqNumMeasure>
                      DelayedGoals = delayedGoals' }

            let delayedGoalStack =
                this.DelayedGoalStack.Pop().Push (delayConjInfo')

            let goalNum =
                { DepthNum = this.CurrentDepth
                  SeqNum = nextSeqNum }

            let addWaitingVar (wg: WaitingGoalsTable) var =
                let waitingGoals =
                    match wg.TryGetValue (var) with
                    | true, waitingGoals -> waitingGoals
                    | _ -> WaitingGoals.Empty

                wg.SetItem (var, waitingGoals.SetItem (goalNum, error.Vars))

            let waitingGoalsTable =
                error.Vars
                |> TagSet.fold addWaitingVar this.WaitingGoals

            { this with
                  DelayedGoalStack = delayedGoalStack
                  WaitingGoals = waitingGoalsTable }

        member private this.addPendingGoal goalNum waitingVars =
            let this' =
                this.deleteWaitingVars goalNum waitingVars

            match this'.PendingGoals.TryGetValue goalNum.DepthNum with
            | true, pendingSeq ->
                { this' with
                      PendingGoals = this'.PendingGoals.SetItem (goalNum.DepthNum, pendingSeq.Add (goalNum.SeqNum)) }
            | _ ->
                let pendingSeq =
                    ImmutableList<SeqNum>.Empty.Add (goalNum.SeqNum)

                { this' with
                      PendingGoals = this'.PendingGoals.SetItem (goalNum.DepthNum, pendingSeq) }

        member this.bindAllVars() =
            this.WaitingGoals
            |> Seq.fold (fun (s: DelayInfo) g -> s.bindVar g.Key) this

        member this.bindVar var : DelayInfo =
            match this.WaitingGoals.TryGetValue (var) with
            | true, waitingGoals ->
                waitingGoals
                |> Seq.fold (fun s g -> s.addPendingGoal g.Key g.Value) this
            | _ -> this

        // Remove all references to a goal from the waiting goals table.
        member private this.deleteWaitingVars goalNum (vars: SetOfVar) : DelayInfo =
            vars
            |> TagSet.fold
                (fun (di: DelayInfo) var ->
                    let waitingGoals = di.WaitingGoals.[var]
                    let waitingGoals' = waitingGoals.Remove (goalNum)

                    if (waitingGoals'.Count = 0) then
                        { di with
                              WaitingGoals = di.WaitingGoals.Remove (var) }
                    else
                        { di with
                              WaitingGoals = di.WaitingGoals.SetItem (var, waitingGoals') })
                this

        member this.wakeupGoals() =
            match this.PendingGoals.TryGetValue this.CurrentDepth with
            | true, pendingGoals ->
                let conjInfo = this.DelayedGoalStack.Peek ()

                let (goals, conjInfo'') =
                    pendingGoals
                    |> Seq.mapFold
                        (fun conjInfo' pg ->
                            let goal = conjInfo.DelayedGoals.[pg]

                            (goal.Goal,
                             { conjInfo' with
                                   DelayedGoals = conjInfo'.DelayedGoals.Remove (pg) }))
                        conjInfo

                let dgs =
                    this.DelayedGoalStack.Pop().Push (conjInfo'')

                (List.ofSeq goals,
                 { this with
                       PendingGoals = this.PendingGoals.SetItem (this.CurrentDepth, ImmutableList<SeqNum>.Empty) })
            | _ -> ([], this)
