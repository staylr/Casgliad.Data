module internal Casgliad.Data.Compiler.DisjunctiveNormalForm

let replaceGoal goal goal' = { goal with Goal = goal' }

type DnfInfo =
    { NewRelations: ResizeArray<RelationInfo>
      mutable Counter: int
      RelationProcId: RelationProcId
      VarSet: VarSet }

let rec goalIsAtomicOrNonRelational goal =
    goalIsAtomic goal
    || not (containsRelationCall goal)
    || match goal.Goal with
       | Not negGoal when goalIsAtomic negGoal -> true
       | Not ({ Goal = Conjunction ({ Goal = Call _ } :: conjGoals) }) when
           List.forall (fun g -> not (containsRelationCall g)) conjGoals
           ->
           true
       | Scope (_, scopeGoal) -> goalIsAtomic scopeGoal
       | _ -> false

let createRelation (dnfInfo: DnfInfo) instMap goal =
    let newRelationName =
        { ModuleName = (fst dnfInfo.RelationProcId).ModuleName
          RelationName = $"dnfInfo.RelationProcId.RelationMame__p{dnfInfo.RelationProcId |> snd}__dnf{dnfInfo.Counter}" }

    do dnfInfo.Counter <- dnfInfo.Counter + 1

    let (newRelation, goal') =
        relationOfGoal newRelationName goal (TagSet.toList (goal.Info.NonLocals)) instMap (dnfInfo.VarSet)

    dnfInfo.NewRelations.Add (newRelation)
    goal'

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
            let goal' = stripTopLevelScopes goal

            let finalGoal =
                if (goalIsAtomicOrNonRelational goal) then
                    goal'
                else
                    let goal'' = dnfProcessGoal dnfInfo instMap' goal'

                    match goal''.Goal with
                    | Not negGoal ->
                        { Goal = Not (createRelation dnfInfo instMap negGoal)
                          Info = goal.Info }
                    | _ -> createRelation dnfInfo instMap goal''

            (finalGoal, instMap'.applyInstMapDelta (goal.Info.InstMapDelta)))
        instMap
    |> fst
