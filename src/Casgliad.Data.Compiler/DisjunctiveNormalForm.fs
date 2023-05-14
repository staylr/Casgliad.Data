module internal Casgliad.Data.Compiler.DisjunctiveNormalForm

type IsLinear =
    | NonLinear
    | LeftLinear
    | RightLinear
    | MultiLinear

type IsRecursive =
    | Recursive
    | NotRecursive

type IsNegated =
    | Negated
    | Positive

type AtomCallee =
    | Relation of RelationProcId * IsRecursive * IsNegated * input: RelationProcId option
    | Input

type AtomExpr =
    | True
    | RelationCall of
        callee: AtomCallee *
        args: VarId list *
        selectProjectCondition: Goal *
        selectProjectOutputs: VarId list
// | Aggregate

type Atom = { Atom: AtomExpr; Info: GoalInfo }

type RuleDefinition = Atom list

type RulesRelation =
    { RelationId: RelationProcId
      OriginalRelationProcId: RelationProcId Option
      SourceInfo: SourceInfo
      Args: VarId list
      Modes: (InstE * BoundInstE) list
      Determinism: Casgliad.Data.Determinism
      ExitRules: RuleDefinition list
      RecursiveRules: RuleDefinition list }

let replaceGoal goal goal' = { goal with Goal = goal' }

type DnfInfo =
    { NewRelations: ResizeArray<RulesRelation>
      mutable Counter: int
      RelationProcId: RelationProcId
      VarSet: VarSet }

let rec goalIsAtomicOrNonRelational goal =
    goalIsAtomic goal
    || not (goal.Info.ContainsRelationCall = Some true)
    || match goal.Goal with
       | Not negGoal when goalIsAtomic negGoal -> true
       | Not({ Goal = Conjunction({ Goal = Call _ } :: conjGoals) }) when
           List.forall (fun g -> not (containsRelationCall g)) conjGoals
           ->
           true
       | Scope(_, scopeGoal) -> goalIsAtomic scopeGoal
       | _ -> false

let rulesRelationOfGoal
    (origName: RelationProcId)
    (name: RelationId)
    (goal: Goal)
    (args: VarId list)
    (instMap0: InstMap)
    (varSet: VarSet)
    : (RulesRelation * Atom) =
    let instMap = instMap0.applyInstMapDelta (goal.Info.InstMapDelta)

    let getArgMode arg =
        let inst0 = instMap0.lookupVar (arg)
        let inst = instMap.lookupVar (arg)

        match inst with
        | Free -> invalidOp $"unexpected unbound argument {arg}"
        | Bound boundInst -> (inst0, boundInst)

    let modes = List.map getArgMode args

    let relationProcId = (name, invalidProcId)

    let newRelation =
        { RulesRelation.RelationId = relationProcId
          OriginalRelationProcId = Some origName
          Args = args
          Modes = modes
          Determinism = goal.Info.Determinism
          SourceInfo = goal.Info.SourceInfo
          ExitRules = []
          RecursiveRules = [] }

    let callee =
        Relation(relationProcId, IsRecursive.NotRecursive, IsNegated.Positive, None)

    let selectProjectCondition = succeedGoal
    let selectProjectOutputs = []

    let goal =
        { Atom = RelationCall(callee, args, selectProjectCondition, selectProjectOutputs)
          Info = goal.Info }

    (newRelation, goal)

let createRelation (dnfInfo: DnfInfo) instMap goal =
    let newRelationName =
        { ModuleName = (fst dnfInfo.RelationProcId).ModuleName
          RelationName = TransformedRelation(dnfInfo.RelationProcId, DisjunctiveNormalFormSubgoal dnfInfo.Counter) }

    do dnfInfo.Counter <- dnfInfo.Counter + 1

    let (newRelation, goal') =
        rulesRelationOfGoal
            dnfInfo.RelationProcId
            newRelationName
            goal
            (TagSet.toList (goal.Info.NonLocals))
            instMap
            (dnfInfo.VarSet)

    dnfInfo.NewRelations.Add(newRelation)
    goal'

let populateContainsRelationCall (goal: GoalExpr) (goalInfo: GoalInfo) (subGoals: Goal seq) =
    let containsCall =
        Some(subGoals |> Seq.exists (fun g -> g.Info.ContainsRelationCall = Some true))

    { Goal = goal
      Info =
        { goalInfo with
            ContainsRelationCall = containsCall } }

let rec dnfPreprocessGoal dnfInfo goal =
    match goal.Goal with
    | Conjunction conjuncts ->
        let conjuncts' = List.map (dnfPreprocessGoal dnfInfo) conjuncts
        populateContainsRelationCall (Conjunction conjuncts') goal.Info conjuncts'
    | Disjunction disjuncts ->
        let disjuncts' = List.map (dnfPreprocessGoal dnfInfo) disjuncts
        populateContainsRelationCall (Conjunction disjuncts') goal.Info disjuncts'
    | Not negGoal ->
        let negGoal' = dnfPreprocessGoal dnfInfo negGoal
        populateContainsRelationCall (Not negGoal') goal.Info [ negGoal' ]
    | Scope(reason, scopeGoal) ->
        let scopeGoal' = dnfPreprocessGoal dnfInfo scopeGoal
        populateContainsRelationCall (Not(dnfPreprocessGoal dnfInfo scopeGoal')) goal.Info [ scopeGoal' ]
    | IfThenElse(condGoal, thenGoal, elseGoal) ->
        let condGoal' = dnfPreprocessGoal dnfInfo condGoal
        let thenGoal' = dnfPreprocessGoal dnfInfo thenGoal
        let elseGoal' = dnfPreprocessGoal dnfInfo elseGoal

        if
            (condGoal'.Info.ContainsRelationCall = Some true
             || thenGoal'.Info.ContainsRelationCall = Some true
             || elseGoal'.Info.ContainsRelationCall = Some true)
        then

            // TODO: rename apart local variables in condition.
            let negatedCond =
                { Goal = Not(condGoal)
                  Info =
                    { condGoal.Info with
                        Determinism = negationDeterminismThrow condGoal.Info.Determinism } }

            let disjunction =
                Disjunction(
                    [ conjoinGoals [ condGoal; thenGoal ] goal.Info
                      conjoinGoals [ negatedCond; elseGoal ] goal.Info ]
                )

            { Goal = disjunction
              Info =
                { goal.Info with
                    ContainsRelationCall = Some true } }
        else
            { Goal = IfThenElse(condGoal', thenGoal', elseGoal')
              Info =
                { goal.Info with
                    ContainsRelationCall = Some false } }
    | Switch _ -> failwith "unexpected switch"
    | Call _ ->
        { Goal = goal.Goal
          Info =
            { goal.Info with
                ContainsRelationCall = Some true } }
    | FSharpCall _
    | Unify _ ->
        { Goal = goal.Goal
          Info =
            { goal.Info with
                ContainsRelationCall = Some false } }


// Convert the goal into a disjunction of conjunctions.
let rec dnfProcessGoal dnfInfo instMap goal =
    let rules =
        match goal.Goal with
        | Disjunction disjuncts -> disjuncts |> List.map (dnfProcessDisjunct dnfInfo instMap)
        | _ -> [ dnfProcessDisjunct dnfInfo instMap goal ]

    rules

and dnfProcessDisjunct dnfInfo instMap goal =
    let rule =
        match goal.Goal with
        | Conjunction conjuncts -> dnfProcessConjunction dnfInfo instMap conjuncts
        | _ -> dnfProcessConjunction dnfInfo instMap [ goal ]

    rule


and dnfProcessConjunction (dnfInfo: DnfInfo) instMap conjuncts = []
//conjuncts
//|> List.mapFold
//    (fun (instMap': InstMap) goal ->
//        let goal' = stripTopLevelScopes goal

//        let finalGoal =
//            if (goalIsAtomicOrNonRelational goal) then
//                goal'
//            else
//                let goal'' = dnfProcessGoal dnfInfo instMap' goal'

//                match goal''.Goal with
//                | Not negGoal ->
//                    { Goal = Not(createRelation dnfInfo instMap negGoal)
//                      Info = goal.Info }
//                | _ -> createRelation dnfInfo instMap goal''

//        (finalGoal, instMap'.applyInstMapDelta (goal.Info.InstMapDelta)))
//    instMap
//|> fst
