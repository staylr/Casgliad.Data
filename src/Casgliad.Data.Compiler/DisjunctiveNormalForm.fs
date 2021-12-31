module internal Casgliad.Data.Compiler.DisjunctiveNormalForm

let replaceGoal goal goal' = { goal with Goal = goal' }

let rec dnfProcessGoal goal =
    if (goalIsAtomic goal
        || not (containsRelationCall goal)
        || match goal.Goal with
           | Not negGoal -> goalIsAtomic negGoal
           | _ -> false) then
        goal
    else
        match goal.Goal with
        | Conjunction conjuncts ->
            dnfProcessConjunction conjuncts
            |> Disjunction
            |> replaceGoal goal
        | Disjunction disjuncts ->
            disjuncts
            |> List.map dnfProcessGoal
            |> Disjunction
            |> replaceGoal goal
        | Not negGoal -> dnfProcessGoal negGoal |> Not |> replaceGoal goal
        | IfThenElse (condGoal, thenGoal, elseGoal) ->
            let negatedCond =
                { Goal = Not (condGoal)
                  Info =
                      { condGoal.Info with
                            Determinism = negationDeterminismThrow condGoal.Info.Determinism } }

            let disjunction =
                Disjunction (
                    [ conjoinGoals [ condGoal; thenGoal ] goal.Info
                      conjoinGoals [ negatedCond; elseGoal ] goal.Info ]
                )

            dnfProcessGoal { Goal = disjunction; Info = goal.Info }
        | Switch _ -> failwith "unexpected switch"
        | Call _
        | FSharpCall _
        | Unify _ -> failwith "unexpected atomic goal"

and dnfProcessConjunction conjuncts = conjuncts
