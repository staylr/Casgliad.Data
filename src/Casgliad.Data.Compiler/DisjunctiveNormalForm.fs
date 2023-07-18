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
    | Negated of negationCondition: Goal
    | Positive

type AtomCallee =
    | Relation of RelationProcId * input: RelationProcId option
    | Input
    | True
    | False

// Queries over base relations don't require magic transformation
// so don't need to be extracted into new relations.
type BaseRelationQuery =
    | BaseRelationAtom of Atom
    | BaseRelationConjunction of BaseRelationQuery list
    | BaseRelationDisjunction of BaseRelationQuery list

and AtomExpr =
    | RelationCall of callee: AtomCallee * args: VarId list * isNegated: IsNegated
    | Query of BaseRelationQuery
// | Aggregate

and Atom =
    { Atom: AtomExpr
      SelectProjectCondition: Goal
      Info: GoalInfo }

type RuleDefinition = Atom list

type RulesRelation =
    { RelationId: RelationProcId
      OriginalRelationProcId: RelationProcId Option
      SourceInfo: SourceInfo
      Args: VarId list
      Modes: (InstE * BoundInstE) list
      Determinism: Casgliad.Data.Determinism
      Rules: RuleDefinition list }

let replaceGoal goal goal' = { goal with Goal = goal' }

type DnfInfo =
    { NewRelations: ResizeArray<RulesRelation>
      mutable Counter: int
      RelationProcId: RelationProcId
      VarSet: VarSet }

let rec goalIsAtomicOrNonRelational goal =
    goalIsAtomic goal
    || not (goal.Info.ContainsRelationCall = Some DerivedRelationCall)
    || match goal.Goal with
       | Not negGoal when goalIsAtomic negGoal -> true
       | Not({ Goal = Conjunction({ Goal = Call _ } :: conjGoals) }) when
           conjGoals
           |> List.forall (fun g -> g.Info.ContainsRelationCall = Some NoRelationCall)
           ->
           true
       | Scope(_, scopeGoal) -> goalIsAtomic scopeGoal
       | _ -> false

let rulesRelationOfGoal
    (origName: RelationProcId)
    (name: RelationId)
    (goal: Goal)
    (rules: RuleDefinition list)
    (args: VarId list)
    (instMap0: InstMap)
    (isNegated: IsNegated)
    (varSet: VarSet)
    : (RulesRelation * AtomExpr) =
    let instMap = instMap0.applyInstMapDelta (goal.Info.InstMapDelta)

    let getArgMode arg =
        let inst0 = instMap0.lookupVar (arg)
        let inst = instMap.lookupVar (arg)

        match inst with
        | Free -> invalidOp $"unexpected unbound argument {arg}"
        | Bound boundInst -> (inst0, boundInst)

    let modes = List.map getArgMode args

    let relationProcId = (name, initialProcId)

    let newRelation =
        { RulesRelation.RelationId = relationProcId
          OriginalRelationProcId = Some origName
          Args = args
          Modes = modes
          Determinism = goal.Info.Determinism
          SourceInfo = goal.Info.SourceInfo
          Rules = rules }

    let callee = Relation(relationProcId, None)

    let atom = RelationCall(callee, args, isNegated)

    (newRelation, atom)

let populateContainsRelationCall (goal: GoalExpr) (goalInfo: GoalInfo) (subGoals: Goal seq) =
    let containsCall = Some(containsRelationCallList subGoals)

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

        let containsRelationCall =
            condGoal'.Info.ContainsRelationCall.Value
            |> combineContainsRelationCall thenGoal'.Info.ContainsRelationCall.Value
            |> combineContainsRelationCall elseGoal'.Info.ContainsRelationCall.Value

        if containsRelationCall <> NoRelationCall then

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
                    ContainsRelationCall = Some containsRelationCall } }
        else
            { Goal = IfThenElse(condGoal', thenGoal', elseGoal')
              Info =
                { goal.Info with
                    ContainsRelationCall = Some NoRelationCall } }
    | Switch _ -> failwith "unexpected switch"
    | Call _ ->
        { Goal = goal.Goal
          Info =
            { goal.Info with
                ContainsRelationCall = Some DerivedRelationCall } }
    | FSharpCall _
    | Unify _ ->
        { Goal = goal.Goal
          Info =
            { goal.Info with
                ContainsRelationCall = Some NoRelationCall } }

let negateAtom (a: Atom) negationCondition =
    match a.Atom with
    | AtomExpr.RelationCall(callee, args, isNegated) ->
        { Atom = AtomExpr.RelationCall(callee, args, IsNegated.Negated negationCondition)
          SelectProjectCondition = a.SelectProjectCondition
          Info = a.Info }

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
        | Conjunction conjuncts -> dnfProcessConjunction dnfInfo instMap conjuncts goal.Info
        | _ -> dnfProcessConjunction dnfInfo instMap [ goal ] goal.Info

    rule

and dnfProcessConjunction (dnfInfo: DnfInfo) instMap conjuncts conjInfo : Atom list =
    dnfProcessConjunction2
        dnfInfo
        instMap
        conjuncts
        conjInfo
        (AtomExpr.RelationCall(AtomCallee.True, [], IsNegated.Positive))
        Goal.succeedGoal.Info
        []

and dnfProcessRelationalGoal (dnfInfo: DnfInfo) (goal: Goal) (instMap: InstMap) : AtomExpr =
    let goal' = stripTopLevelScopes goal

    match goal'.Goal with
    | Call(callee, args) -> AtomExpr.RelationCall(AtomCallee.Relation(callee, None), args, IsNegated.Positive)
    | _ -> createRelation dnfInfo instMap goal' IsNegated.Positive

//let finalGoal =
//    if (goalIsAtomicOrNonRelational goal') then
//        goal'
//    else
//        match goal'.Goal with
//        | Not negGoal -> createRelation dnfInfo instMap negGoal |> negateAtom
//        | _ -> createRelation dnfInfo instMap goal'

and dnfProcessConjunction2 dnfInfo (instMap: InstMap) conjuncts conjInfo currentCallee currentCallInfo revAtoms =
    let nonRelational = List.takeWhile goalIsAtomicOrNonRelational conjuncts
    let nonRelationalConj = conjoinGoals nonRelational conjInfo

    let instMap' = instMap.applyInstMapDelta (currentCallInfo.InstMapDelta)
    let instMap'' = instMap'.applyInstMapDelta (nonRelationalConj.Info.InstMapDelta)

    let atom =
        { Atom = currentCallee
          SelectProjectCondition = nonRelationalConj
          Info = conjInfo }

    let revAtoms' = atom :: revAtoms

    let remainingConjuncts = List.skip (List.length nonRelational) conjuncts

    match remainingConjuncts with
    | [] -> revAtoms' |> List.rev
    | nextCall :: remainingConjuncts' ->
        let nextCallee = dnfProcessRelationalGoal dnfInfo nextCall instMap

        dnfProcessConjunction2 dnfInfo instMap'' remainingConjuncts' conjInfo nextCallee (nextCall.Info) revAtoms'

and createRelation (dnfInfo: DnfInfo) instMap goal isNegated =
    let newRelationName =
        { ModuleName = (fst dnfInfo.RelationProcId).ModuleName
          RelationName = TransformedRelation(dnfInfo.RelationProcId, DisjunctiveNormalFormSubgoal dnfInfo.Counter) }

    do dnfInfo.Counter <- dnfInfo.Counter + 1

    let rules = dnfProcessGoal dnfInfo instMap goal

    let (newRelation, callExpr) =
        rulesRelationOfGoal
            dnfInfo.RelationProcId
            newRelationName
            goal
            rules
            (TagSet.toList (goal.Info.NonLocals))
            instMap
            isNegated
            (dnfInfo.VarSet)

    dnfInfo.NewRelations.Add(newRelation)

    callExpr
