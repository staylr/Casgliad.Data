module internal Kanren.Data.Compiler.DeterminismAnalysis

open Kanren.Data
open Kanren.Data.Compiler.DeterminismErrors

type FailingGoal =
    | IncompleteSwitch of VarId
    | FailGoal
    | TestGoal of VarId * VarId
    | DeconstructGoal of VarId * Constructor
    | CallGoal of RelationProcId
    | FSharpCallGoal of FSharpProcId
    | NegatedGoal

type FailingContext =
    { Context: SourceInfo
      Goal: FailingGoal }

type DeterminismInfo =
    { LookupRelationModes: ModeInfo.LookupRelationModes
      LookupFSharpFunctionModes: ModeInfo.LookupFSharpFunctionModes
      CurrentRelation: RelationProcId
      VarSet: VarSet
      InstTable: InstTable
      Errors: ResizeArray<DeterminismErrorInfo>
      Warnings: ResizeArray<DeterminismWarningInfo> }

let rec determinismInferGoal detInfo (goal: Goal) (instMap0: InstMap) solutionContext rightFailingContexts =
    let (solutionContext', addPruning) =
        if (instMap0.hasOutputVars detInfo.InstTable detInfo.VarSet instMap0 goal.Info.NonLocals) then
            (solutionContext, false)
        else
            (FirstSolution, true)

    let addPruning' =
        match goal.Goal with
        | Scope (Commit, _) -> true
        | _ -> addPruning

    let (goalExpr', internalDeterminism0, goalFailingContexts) =
        determinismInferGoalExpr detInfo goal.Goal goal.Info instMap0 solutionContext' rightFailingContexts

    let (internalMaxSolutions0, internalCanFail) =
        determinismComponents internalDeterminism0

    let internalMaxSolutions =
        if (not (goal.Info.InstMapDelta.isReachable ())) then
            NoSolutions
        else
            internalMaxSolutions0

    let maxSolutions =
        if (addPruning'
            && (internalMaxSolutions = MoreThanOneSolution
                || internalMaxSolutions = CommittedChoice)) then
            OneSolution
        else
            internalMaxSolutions

    let determinism =
        determinismFromComponents maxSolutions internalCanFail

    let goalInfo' =
        { goal.Info with
              Determinism = determinism }


    // The code generator assumes that conjunctions containing multi or nondet
    // goals and if-then-elses containing multi or nondet conditions can only
    // occur inside other multi or nondet goals.
    let finalInternalSolutions =
        match goalExpr' with
        | IfThenElse ({ Goal = _; Info = condInfo }, _, _) when
            maxSolutions <> MoreThanOneSolution
            && (determinismComponents condInfo.Determinism |> fst) = MoreThanOneSolution
            ->
            MoreThanOneSolution
        | Conjunction (conjGoals) when
            maxSolutions = NoSolutions
            && conjGoals
               |> List.exists
                   (fun conjGoal ->
                       (determinismComponents conjGoal.Info.Determinism
                        |> fst) = MoreThanOneSolution)
            ->
            MoreThanOneSolution
        | _ -> internalMaxSolutions

    let finalInternalDeterminism =
        determinismFromComponents finalInternalSolutions internalCanFail

    let needCommit =
        if (determinism <> finalInternalDeterminism) then
            match goalExpr' with
            | Disjunction _
            | Scope _ -> true
            | _ -> false
        else
            false

    let goalExpr'' =
        if needCommit then
            Scope (
                Commit,
                { Goal = goalExpr'
                  Info =
                      { goal.Info with
                            Determinism = finalInternalDeterminism } }
            )
        else
            goalExpr'

    ({ Goal = goalExpr''; Info = goalInfo' }, determinism, goalFailingContexts)

and determinismInferGoalExpr
    detInfo
    goalExpr
    goalInfo
    instMap0
    solutionContext
    rightFailingContexts
    : GoalExpr * Determinism * FailingContext list =
    match goalExpr with
    | Conjunction (conjGoals) ->
        let (conjGoals', determinism, conjFailingContexts) =
            determinismInferConjunction detInfo conjGoals instMap0 solutionContext rightFailingContexts []

        (Conjunction (conjGoals'), determinism, conjFailingContexts)
    | Disjunction (disjGoals) ->
        let (disjGoals, determinism, failingContexts) =
            determinismInferDisjunction
                detInfo
                disjGoals
                instMap0
                solutionContext
                rightFailingContexts
                CanFail
                NoSolutions
                []

        match disjGoals with
        | [] ->
            (Disjunction ([]),
             Fail,
             { Context = goalInfo.SourceInfo
               Goal = FailGoal }
             :: failingContexts)
        | _ :: _ -> (Disjunction (disjGoals), determinism, failingContexts)
    | Call (callee, args) -> determinismInferCall detInfo callee args goalInfo solutionContext rightFailingContexts
    | FSharpCall (callee, args, retVal) ->
        determinismInferFSharpCall detInfo callee args retVal goalInfo solutionContext rightFailingContexts
    | Unify (lhs, rhs, mode, context) ->
        determinismInferUnify detInfo lhs rhs mode context goalInfo instMap0 solutionContext rightFailingContexts


and determinismInferUnify detInfo lhs rhs mode context goalInfo instMap0 solutionContext rightFailingContexts =
    let inferUnifyFailingGoal lhs rhs =
        match rhs with
        | Var (_, Assign) -> None
        | Var (rhsVar, Test) ->
            Some (
                { Context = goalInfo.SourceInfo
                  Goal = TestGoal (lhs, rhsVar) }
            )
        | Constructor (ctor, _, _, _, canFail) ->
            match canFail with
            | CanFail ->
                Some (
                    { Context = goalInfo.SourceInfo
                      Goal = DeconstructGoal (lhs, ctor) }
                )
            | CannotFail -> None
        | Lambda _ -> None

    // TODO: check lambda goal
    let goal = Unify (lhs, rhs, mode, context)

    let maybeFailingGoal = inferUnifyFailingGoal lhs rhs

    match maybeFailingGoal with
    | Some (failingGoal) -> (goal, determinismFromComponents OneSolution CanFail, [ failingGoal ])
    | None -> (goal, Det, [])


and determinismInferDisjunction
    detInfo
    disjGoals
    instMap0
    solutionContext
    rightFailingContexts
    canFail
    numSolutions
    failingContexts
    =
    match disjGoals with
    | [] -> ([], determinismFromComponents numSolutions canFail, failingContexts)
    | goal :: goals ->
        let (goal', goalDeterminism, goalFailingContexts) =
            determinismInferGoal detInfo goal instMap0 solutionContext rightFailingContexts

        let (firstNumSolutions, firstCanFail) = determinismComponents goalDeterminism

        let canFail' =
            detDisjunctionCanFail canFail firstCanFail

        let numSolutions' =
            detDisjunctionMaxSoln numSolutions firstNumSolutions

        let numSolutions'' =
            if (solutionContext = FirstSolution
                && numSolutions' = MoreThanOneSolution) then
                CommittedChoice
            else
                numSolutions'

        let (goals', determinism, disjFailingContexts) =
            determinismInferDisjunction
                detInfo
                goals
                instMap0
                solutionContext
                rightFailingContexts
                canFail'
                numSolutions''
                failingContexts

        (goal' :: goals', determinism, List.append goalFailingContexts disjFailingContexts)

and determinismInferFSharpCall detInfo callee args retVal goalInfo solutionContext rightFailingContexts =
    let modes =
        detInfo.LookupFSharpFunctionModes (fst callee)
        |> List.find (fun m -> m.ProcId = snd callee)

    let (numSolutions, canFail) =
        determinismComponents modes.Modes.Determinism

    if (numSolutions = CommittedChoice
        && solutionContext = AllSolutions) then
        failwith
            $"Error: call to {callee} with determinism {modes.Modes.Determinism} occurs in a context which requires all solutions"

    let goalFailingContexts =
        match canFail with
        | CanFail ->
            [ { Context = goalInfo.SourceInfo
                Goal = FailingGoal.FSharpCallGoal callee } ]
        | CannotFail -> []

    (FSharpCall (callee, args, retVal), modes.Modes.Determinism, goalFailingContexts)

and determinismInferCall detInfo callee args goalInfo solutionContext rightFailingContexts =
    let modes =
        detInfo.LookupRelationModes (fst callee)
        |> List.find (fun m -> m.ProcId = snd callee)

    let (numSolutions, canFail) =
        determinismComponents modes.Modes.Determinism

    if (numSolutions = CommittedChoice
        && solutionContext = AllSolutions) then
        detInfo.Errors.Add (
            { SourceInfo = goalInfo.SourceInfo
              Relation = detInfo.CurrentRelation
              Error = CallMustBeInSingleSolutionContext callee }
        )

    let goalFailingContexts =
        match canFail with
        | CanFail ->
            [ { Context = goalInfo.SourceInfo
                Goal = CallGoal callee } ]
        | CannotFail -> []

    (Call (callee, args), modes.Modes.Determinism, goalFailingContexts)


and determinismInferConjunction detInfo conjGoals instMap0 solutionContext rightFailingContexts conjFailingContexts =
    match conjGoals with
    | headGoal :: tailGoals ->
        let instMap1 =
            instMap0.applyInstMapDelta headGoal.Info.InstMapDelta

        let (tailGoals', tailDeterminism, conjFailingContexts') =
            determinismInferConjunction
                detInfo
                tailGoals
                instMap1
                solutionContext
                rightFailingContexts
                conjFailingContexts

        let tailCanFail =
            determinismComponents tailDeterminism |> snd

        let headSolutionContext =
            if (tailCanFail = CannotFail
                && solutionContext = FirstSolution) then
                FirstSolution
            else
                AllSolutions

        let (headGoal', headDeterminism, headFailingContexts) =
            determinismInferGoal
                detInfo
                headGoal
                instMap0
                headSolutionContext
                (List.append conjFailingContexts' rightFailingContexts)

        let determinism =
            conjunctionDeterminism headDeterminism tailDeterminism

        let conjFailingContexts'' =
            List.append headFailingContexts conjFailingContexts'

        (headGoal' :: tailGoals', determinism, conjFailingContexts'')
    | [] -> ([], Det, conjFailingContexts)

let determinismInferProcedureBody
    instTable
    relationProcId
    args
    argModes
    declaredDet
    varSet
    goal
    lookupRelationModes
    lookupFSharpModes
    =
    let detInfo =
        { InstTable = instTable
          VarSet = varSet
          LookupRelationModes = lookupRelationModes
          LookupFSharpFunctionModes = lookupFSharpModes
          CurrentRelation = relationProcId
          Errors = ResizeArray ()
          Warnings = ResizeArray () }

    let instMap = InstMap.ofInitialArgModes args argModes

    let solutionContext =
        SolutionContext.ofDeterminism declaredDet

    let (goal', inferredDet, _) =
        determinismInferGoal detInfo goal instMap solutionContext []

    let compareDeterminism =
        compareDeterminisms declaredDet inferredDet

    match compareDeterminism with
    | DeterminismComparison.FirstSameAs -> ()
    | DeterminismComparison.FirstTighterThan ->
        detInfo.Warnings.Add (
            { Relation = relationProcId
              SourceInfo = goal.Info.SourceInfo
              Warning = DeterminismWarning.DeclarationTooLax (declaredDet, inferredDet) }
        )
    | DeterminismComparison.FirstLooserThan
    | DeterminismComparison.Incomparable ->
        // TODO: diagnose error.
        detInfo.Errors.Add (
            { Relation = relationProcId
              SourceInfo = goal.Info.SourceInfo
              Error = DeterminismError.DeclarationNotSatisfied (declaredDet, inferredDet, []) }
        )

    (goal', detInfo.Errors, detInfo.Warnings, inferredDet)
