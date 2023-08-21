module internal Casgliad.Data.Compiler.DeterminismAnalysis

open Casgliad.Data
open Casgliad.Data.Compiler.DeterminismErrors

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

let rec determinismDiagnoseGoal
    detInfo
    (goal: Goal)
    (instMap0: InstMap)
    (desired: Determinism)
    (switchContext: DeterminismSwitchContext list)
    : DeterminismDiagnosisInfo list =
    let comparisonResult = compareDeterminisms desired goal.Info.Determinism

    match comparisonResult with
    | DeterminismComparison.Incomparable
    | DeterminismComparison.FirstTighterThan ->
        determinismDiagnoseGoalExpr detInfo goal instMap0 desired goal.Info.Determinism switchContext
    | DeterminismComparison.FirstLooserThan
    | DeterminismComparison.FirstSameAs -> []

and determinismDiagnoseGoalExpr
    detInfo
    (goal: Goal)
    (instMap0: InstMap)
    (desired: Determinism)
    (actual: Determinism)
    (switchContext: DeterminismSwitchContext list)
    : DeterminismDiagnosisInfo list =
    match goal.Goal with
    | Conjunction conjuncts -> determinismDiagnoseConjunction detInfo conjuncts instMap0 desired switchContext
    | Disjunction disjuncts ->
        let msgs =
            determinismDiagnoseDisjunction detInfo disjuncts instMap0 desired actual switchContext

        let desiredMaxSoln = determinismComponents goal.Info.Determinism |> fst

        if (desiredMaxSoln <> MoreThanOneSolution && desiredMaxSoln <> CommittedChoice) then

            let disjunctsWithSolution =
                disjuncts
                |> Seq.filter (fun disjunct -> disjunct.Info.Determinism |> determinismComponents |> fst <> NoSolutions)
                |> Seq.length

            if (disjunctsWithSolution > 1) then
                { Diagnosis = DiagnosisDisjunctionHasMultipleClausesWithSolutions
                  Context = DeterminismDiagnosisContextNone
                  SwitchContext = switchContext
                  SourceInfo = goal.Info.SourceInfo }
                :: msgs
            else
                msgs
        else
            msgs
    | IfThenElse(condGoal, thenGoal, elseGoal) ->
        let desiredMaxSoln = determinismComponents goal.Info.Determinism |> fst
        let condMaxSoln = determinismComponents condGoal.Info.Determinism |> fst

        let condMsgs =
            if (condMaxSoln = MoreThanOneSolution && desiredMaxSoln <> MoreThanOneSolution) then
                let desiredCond = determinismFromComponents desiredMaxSoln CanFail
                determinismDiagnoseGoal detInfo condGoal instMap0 desiredCond switchContext
            else
                []

        let instMap1 = instMap0.applyInstMapDelta (condGoal.Info.InstMapDelta)

        let thenMsgs =
            determinismDiagnoseGoal detInfo thenGoal instMap1 desired switchContext

        let elseMsgs =
            determinismDiagnoseGoal detInfo elseGoal instMap0 desired switchContext

        List.concat [ condMsgs; thenMsgs; elseMsgs ]
    | Not(negGoal) ->
        let (desiredMaxSoln, desiredCanFail) = determinismComponents desired
        let (actualMaxSoln, actualCanFail) = determinismComponents actual

        if (desiredCanFail = CannotFail && actualCanFail = CanFail) then
            [ { Diagnosis = DiagnosisNegatedGoalCanSucceed
                Context = DeterminismDiagnosisContextNone
                SwitchContext = switchContext
                SourceInfo = goal.Info.SourceInfo } ]
        else if (desiredMaxSoln = NoSolutions && actualMaxSoln <> NoSolutions) then
            [ { Diagnosis = DiagnosisNegatedGoalCanFail
                Context = DeterminismDiagnosisContextNone
                SwitchContext = switchContext
                SourceInfo = goal.Info.SourceInfo } ]
        else
            []
    | Scope(_, scopeGoal) ->
        let internalDesired =
            if (actual = scopeGoal.Info.Determinism) then
                desired
            else
                // The scope is a commit.
                let desiredCanFail = determinismComponents desired |> snd
                determinismFromComponents MoreThanOneSolution desiredCanFail

        determinismDiagnoseGoal detInfo scopeGoal instMap0 internalDesired switchContext

    | Unify(lhs, rhs, _, context) ->
        determinismDiagnosePrimitiveGoal
            desired
            actual
            goal.Info.SourceInfo
            (DeterminismDiagnosisContextUnify(lhs, rhs, context))
            switchContext
    | Call(callee, args) ->
        determinismDiagnosePrimitiveGoal
            desired
            actual
            goal.Info.SourceInfo
            (DeterminismDiagnosisContextCall(callee, args))
            switchContext
    | FSharpCall(callee, _, args) ->
        determinismDiagnosePrimitiveGoal
            desired
            actual
            goal.Info.SourceInfo
            (DeterminismDiagnosisContextFSharpCall(callee, args))
            switchContext

and determinismDiagnosePrimitiveGoal
    (desired: Determinism)
    (actual: Determinism)
    sourceInfo
    diagnosisContext
    switchContext
    =

    let (desiredSolutions, desiredCanFail) = determinismComponents desired
    let (actualSolutions, actualCanFail) = determinismComponents actual

    let canFailMessages =
        match (compareCanFails desiredCanFail actualCanFail) with
        | FirstTighterThan ->
            [ { Diagnosis = DiagnosisGoalCanFail
                Context = diagnosisContext
                SwitchContext = switchContext
                SourceInfo = sourceInfo } ]
        | FirstSameAs
        | FirstLooserThan -> []

    let solutionsMessages =
        match (compareSolutionCount desiredSolutions actualSolutions) with
        | FirstTighterThan ->
            let diagnosis =
                match desiredSolutions with
                | OneSolution -> DiagnosisGoalCanSucceedMoreThanOnce
                | NoSolutions
                | MoreThanOneSolution
                | CommittedChoice -> DiagnosisGoalCanSucceed

            [ { Diagnosis = diagnosis
                Context = diagnosisContext
                SwitchContext = switchContext
                SourceInfo = sourceInfo } ]
        | FirstSameAs
        | FirstLooserThan -> []

    let diagnoses = List.append canFailMessages solutionsMessages

    if (diagnoses <> []) then
        diagnoses
    else
        [ { Diagnosis = DiagnosisUnknown(desired, actual)
            Context = diagnosisContext
            SwitchContext = switchContext
            SourceInfo = sourceInfo } ]

and determinismDiagnoseConjunction
    detInfo
    (goals: Goal list)
    (instMap0: InstMap)
    (desired: Determinism)
    (switchContext: DeterminismSwitchContext list)
    : DeterminismDiagnosisInfo list =
    match goals with
    | [] -> []
    | goal :: goals ->
        let instMap1 = instMap0.applyInstMapDelta goal.Info.InstMapDelta

        List.append
            (determinismDiagnoseGoal detInfo goal instMap0 desired switchContext)
            (determinismDiagnoseConjunction detInfo goals instMap1 desired switchContext)

and determinismDiagnoseDisjunction detInfo goals instMap0 desired actual switchContext =
    match goals with
    | [] -> []
    | goal :: goals' ->
        let (_, actualCanFail) = determinismComponents actual
        let (desiredMaxSoln, desiredCanFail) = determinismComponents desired

        let clauseCanFail =
            if (desiredCanFail = CannotFail && actualCanFail = CanFail) then
                CannotFail
            else
                CanFail

        let clauseDesired = determinismFromComponents desiredMaxSoln clauseCanFail

        List.append
            (determinismDiagnoseGoal detInfo goal instMap0 clauseDesired switchContext)
            (determinismDiagnoseDisjunction detInfo goals' instMap0 desired actual switchContext)

let rec determinismInferGoal detInfo (goal: Goal) (instMap0: InstMap) solutionContext rightFailingContexts =
    let (solutionContext', addPruning) =
        if (instMap0.hasOutputVars detInfo.InstTable detInfo.VarSet instMap0 goal.Info.NonLocals) then
            (solutionContext, false)
        else
            (FirstSolution, true)

    let addPruning' =
        match goal.Goal with
        | Scope(Commit, _) -> true
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
        if
            (addPruning'
             && (internalMaxSolutions = MoreThanOneSolution
                 || internalMaxSolutions = CommittedChoice))
        then
            OneSolution
        else
            internalMaxSolutions

    let determinism = determinismFromComponents maxSolutions internalCanFail

    let goalInfo' =
        { goal.Info with
            Determinism = determinism }


    // The code generator assumes that conjunctions containing multi or nondet
    // goals and if-then-elses containing multi or nondet conditions can only
    // occur inside other multi or nondet goals.
    let finalInternalSolutions =
        match goalExpr' with
        | IfThenElse({ Goal = _; Info = condInfo }, _, _) when
            maxSolutions <> MoreThanOneSolution
            && (determinismComponents condInfo.Determinism |> fst) = MoreThanOneSolution
            ->
            MoreThanOneSolution
        | Conjunction(conjGoals) when
            maxSolutions = NoSolutions
            && conjGoals
               |> List.exists (fun conjGoal ->
                   (determinismComponents conjGoal.Info.Determinism |> fst) = MoreThanOneSolution)
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
            Scope(
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
    | Conjunction(conjGoals) ->
        let (conjGoals', determinism, conjFailingContexts) =
            determinismInferConjunction detInfo conjGoals instMap0 solutionContext rightFailingContexts []

        (Conjunction(conjGoals'), determinism, conjFailingContexts)
    | Disjunction(disjGoals) ->
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
            (Disjunction([]),
             Fail,
             { Context = goalInfo.SourceInfo
               Goal = FailGoal }
             :: failingContexts)
        | _ :: _ -> (Disjunction(disjGoals), determinism, failingContexts)
    | Call(callee, args) -> determinismInferCall detInfo callee args goalInfo solutionContext rightFailingContexts
    | FSharpCall(callee, args, retVal) ->
        determinismInferFSharpCall detInfo callee args retVal goalInfo solutionContext rightFailingContexts
    | Unify(lhs, rhs, mode, context) ->
        determinismInferUnify detInfo lhs rhs mode context goalInfo instMap0 solutionContext rightFailingContexts
    | IfThenElse(condGoal, thenGoal, elseGoal) ->
        determinismInferIfThenElse
            detInfo
            condGoal
            thenGoal
            elseGoal
            goalInfo
            instMap0
            solutionContext
            rightFailingContexts
    | Not(negatedGoal) -> determinismInferNot detInfo negatedGoal goalInfo instMap0 solutionContext rightFailingContexts
    | Scope(scopeReason, scopeGoal) ->
        let (scopeGoal', scopeGoalDeterminism, scopeFailingContexts) =
            determinismInferGoal detInfo scopeGoal instMap0 solutionContext rightFailingContexts

        (Scope(scopeReason, scopeGoal'), scopeGoalDeterminism, scopeFailingContexts)
    | Switch(_, _, _) -> failwith "switch not supported"

and determinismInferNot detInfo goal goalInfo instMap0 solutionContext rightFailingContexts =
    let (goal', goalDeterminism, _) =
        determinismInferGoal detInfo goal instMap0 FirstSolution []

    match negationDeterminism goalDeterminism with
    | Some(negatedDeterminism) ->
        let goalFailingContexts =
            match determinismComponents negatedDeterminism |> snd with
            | CanFail ->
                [ { Goal = FailingGoal.NegatedGoal
                    Context = goalInfo.SourceInfo } ]
            | CannotFail -> []

        (Not(goal'), negatedDeterminism, goalFailingContexts)
    | None -> failwith "inappropriate determinism inside a negation"

and determinismInferIfThenElse
    detInfo
    condGoal
    thenGoal
    elseGoal
    goalInfo
    instMap0
    solutionContext
    rightFailingContexts
    =
    let instMap1 = instMap0.applyInstMapDelta condGoal.Info.InstMapDelta

    let (thenGoal', thenDeterminism, thenFailingContexts) =
        determinismInferGoal detInfo thenGoal instMap1 solutionContext rightFailingContexts

    let (thenMaxSolutions, thenCanFail) = determinismComponents thenDeterminism

    let condSolutionContext =
        if thenCanFail = CannotFail && solutionContext = FirstSolution then
            FirstSolution
        else
            AllSolutions

    let (condGoal', condDeterminism, _) =
        determinismInferGoal
            detInfo
            condGoal
            instMap0
            condSolutionContext
            (List.append thenFailingContexts rightFailingContexts)

    let (condMaxSolutions, condCanFail) = determinismComponents condDeterminism

    let (elseGoal', elseDeterminism, elseFailingContexts) =
        determinismInferGoal detInfo elseGoal instMap0 solutionContext rightFailingContexts

    let (elseMaxSolutions, elseCanFail) = determinismComponents elseDeterminism

    // Put it all together.
    let determinism =
        match condCanFail with
        | CannotFail ->
            // Ignore the else part, it can't be reached..
            conjunctionDeterminism condDeterminism thenDeterminism
        | CanFail ->
            match condMaxSolutions with
            | NoSolutions ->
                match negationDeterminism condDeterminism with
                | Some(negDeterminism) ->
                    // Ignore the then part, it can't be reached.
                    conjunctionDeterminism negDeterminism elseDeterminism
                | None -> failwith "cannot find determinism of negated condition"
            | OneSolution
            | MoreThanOneSolution
            | CommittedChoice ->
                let condThenMaxSolutions = detConjunctionMaxSoln condMaxSolutions thenMaxSolutions

                let maxSolutions = detSwitchMaxSoln condThenMaxSolutions elseMaxSolutions

                let canFail = detSwitchCanFail thenCanFail elseCanFail
                determinismFromComponents maxSolutions canFail

    let goal = IfThenElse(condGoal', thenGoal', elseGoal')

    (goal, determinism, List.append thenFailingContexts elseFailingContexts)

and determinismInferUnify detInfo lhs rhs mode context goalInfo instMap0 solutionContext rightFailingContexts =
    let inferUnifyFailingGoal lhs rhs =
        match rhs with
        | Var(_, Assign) -> None
        | Var(rhsVar, Test) ->
            Some(
                { Context = goalInfo.SourceInfo
                  Goal = TestGoal(lhs, rhsVar) }
            )
        | Constructor(ctor, _, _, _, canFail) ->
            match canFail with
            | CanFail ->
                Some(
                    { Context = goalInfo.SourceInfo
                      Goal = DeconstructGoal(lhs, ctor) }
                )
            | CannotFail -> None
        | Lambda _ -> None

    // TODO: check lambda goal
    let goal = Unify(lhs, rhs, mode, context)

    let maybeFailingGoal = inferUnifyFailingGoal lhs rhs

    match maybeFailingGoal with
    | Some(failingGoal) -> (goal, determinismFromComponents OneSolution CanFail, [ failingGoal ])
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

        let canFail' = detDisjunctionCanFail canFail firstCanFail

        let numSolutions' = detDisjunctionMaxSoln numSolutions firstNumSolutions

        let numSolutions'' =
            if (solutionContext = FirstSolution && numSolutions' = MoreThanOneSolution) then
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
        detInfo.LookupFSharpFunctionModes(fst callee)
        |> List.find (fun m -> m.ProcId = snd callee)

    let (numSolutions, canFail) = determinismComponents modes.Modes.Determinism

    if (numSolutions = CommittedChoice && solutionContext = AllSolutions) then
        failwith
            $"Error: call to {callee} with determinism {modes.Modes.Determinism} occurs in a context which requires all solutions"

    let goalFailingContexts =
        match canFail with
        | CanFail ->
            [ { Context = goalInfo.SourceInfo
                Goal = FailingGoal.FSharpCallGoal callee } ]
        | CannotFail -> []

    (FSharpCall(callee, args, retVal), modes.Modes.Determinism, goalFailingContexts)

and determinismInferCall detInfo callee args goalInfo solutionContext rightFailingContexts =
    let modes =
        detInfo.LookupRelationModes(fst callee)
        |> List.find (fun m -> m.ProcId = snd callee)

    let (numSolutions, canFail) = determinismComponents modes.Modes.Determinism

    if (numSolutions = CommittedChoice && solutionContext = AllSolutions) then
        detInfo.Errors.Add(
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

    (Call(callee, args), modes.Modes.Determinism, goalFailingContexts)

and determinismInferConjunction detInfo conjGoals instMap0 solutionContext rightFailingContexts conjFailingContexts =
    match conjGoals with
    | headGoal :: tailGoals ->
        let instMap1 = instMap0.applyInstMapDelta headGoal.Info.InstMapDelta

        let (tailGoals', tailDeterminism, conjFailingContexts') =
            determinismInferConjunction
                detInfo
                tailGoals
                instMap1
                solutionContext
                rightFailingContexts
                conjFailingContexts

        let tailCanFail = determinismComponents tailDeterminism |> snd

        let headSolutionContext =
            if (tailCanFail = CannotFail && solutionContext = FirstSolution) then
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

        let determinism = conjunctionDeterminism headDeterminism tailDeterminism

        let conjFailingContexts'' = List.append headFailingContexts conjFailingContexts'

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
          Errors = ResizeArray()
          Warnings = ResizeArray() }

    let instMap = InstMap.ofInitialArgModes args argModes

    let solutionContext = SolutionContext.ofDeterminism declaredDet

    let (goal', inferredDet, _) =
        determinismInferGoal detInfo goal instMap solutionContext []

    let compareDeterminism = compareDeterminisms declaredDet inferredDet

    match compareDeterminism with
    | DeterminismComparison.FirstSameAs -> ()
    | DeterminismComparison.FirstTighterThan ->
        detInfo.Warnings.Add(
            { Relation = relationProcId
              SourceInfo = goal'.Info.SourceInfo
              Warning = DeterminismWarning.DeclarationTooLax(declaredDet, inferredDet) }
        )
    | DeterminismComparison.FirstLooserThan
    | DeterminismComparison.Incomparable ->
        let diagnoses = determinismDiagnoseGoal detInfo goal' instMap declaredDet []

        detInfo.Errors.Add(
            { Relation = relationProcId
              SourceInfo = goal'.Info.SourceInfo
              Error = DeterminismError.DeclarationNotSatisfied(declaredDet, inferredDet, diagnoses) }
        )

    (goal', detInfo.Errors |> List.ofSeq, detInfo.Warnings |> List.ofSeq, inferredDet)

let determinismInferProcedure
    lookupRelationModes
    lookupFunctionModes
    (relationProcId: RelationProcId)
    (_relationInfo: RelationInfo)
    (procInfo: ProcInfo)
    (moduleInfo: ModuleInfo)
    =
    let (goal, errors, warnings, inferredDet) =
        determinismInferProcedureBody
            moduleInfo.InstTable
            relationProcId
            procInfo.Args
            procInfo.Modes
            procInfo.Determinism
            procInfo.VarSet
            procInfo.ProcGoal
            lookupRelationModes
            lookupFunctionModes

    (errors,
     warnings,
     { procInfo with
         InferredDeterminism = Some inferredDet
         ProcGoal = goal })

let determinismInferModule (moduleInfo: ModuleInfo) =
    let detErrors = ResizeArray()
    let detWarnings = ResizeArray()

    moduleInfo.processProcedures (fun relProcId relInfo procInfo moduleInfo ->
        let procErrors, procWarnings, procInfo' =
            determinismInferProcedure
                (Modecheck.lookupArgModesInModuleInfo moduleInfo)
                Casgliad.Data.Compiler.Builtins.lookupFSharpFunctionModes
                relProcId
                relInfo
                procInfo
                moduleInfo

        detErrors.AddRange(procErrors)
        detWarnings.AddRange(procWarnings)
        procInfo')

    (detErrors |> List.ofSeq, detWarnings |> List.ofSeq)
