module internal Casgliad.Data.Compiler.DisjunctiveNormalForm

let replaceGoal goal goal' = { goal with Goal = goal' }

type DnfInfo =
    { NewRelations: ResizeArray<RelationInfo>
      mutable Counter: int
      RelationProcId: RelationProcId
      VarSet: VarSet }

let goalIsAtomicOrNonRelational goal =
    goalIsAtomic goal
    || not (containsRelationCall goal)
    || match goal.Goal with
       | Not negGoal -> goalIsAtomic negGoal
       | Scope (_, scopeGoal) -> goalIsAtomic scopeGoal
       | _ -> false

let rec dnfProcessGoal dnfInfo instMap goal =
    if (goalIsAtomicOrNonRelational goal) then
        goal
    else
        match goal.Goal with
        | Conjunction conjuncts ->
            dnfProcessConjunction dnfInfo instMap conjuncts
            |> Disjunction
            |> replaceGoal goal
        | Disjunction disjuncts ->
            disjuncts
            |> List.map (dnfProcessGoal dnfInfo instMap)
            |> Disjunction
            |> replaceGoal goal
        | Not negGoal ->
            dnfProcessGoal dnfInfo instMap negGoal
            |> Not
            |> replaceGoal goal
        | Scope (reason, scopeGoal) ->
            let scopeGoal' = dnfProcessGoal dnfInfo instMap scopeGoal
            Scope (reason, scopeGoal') |> replaceGoal goal
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

            dnfProcessGoal dnfInfo instMap { Goal = disjunction; Info = goal.Info }
        | Switch _ -> failwith "unexpected switch"
        | Call _
        | FSharpCall _
        | Unify _ -> failwith "unexpected atomic goal"

and dnfProcessConjunction (dnfInfo: DnfInfo) instMap conjuncts =
    conjuncts
    |> List.mapFold
        (fun (instMap': InstMap) goal ->
            let goal' =
                if (goalIsAtomicOrNonRelational goal) then
                    goal
                else
                    let newRelationName =
                        { ModuleName = (fst dnfInfo.RelationProcId).ModuleName
                          RelationName =
                              $"dnfInfo.RelationProcId.RelationMame__p{dnfInfo.RelationProcId |> snd}__dnf{dnfInfo.Counter}" }

                    do dnfInfo.Counter <- dnfInfo.Counter + 1

                    let (newRelation, goal'') =
                        relationOfGoal
                            newRelationName
                            goal
                            (TagSet.toList (goal.Info.NonLocals))
                            instMap
                            (dnfInfo.VarSet)

                    dnfInfo.NewRelations.Add (newRelation)
                    goal''

            (dnfProcessGoal dnfInfo instMap' goal, instMap'.applyInstMapDelta (goal.Info.InstMapDelta)))
        instMap
    |> fst
