module internal Casgliad.Data.Compiler.DeterminismErrors

open Casgliad.Data

type DeterminismDiagnosis =
    | DisjunctionHasMultipleClausesWithSolutions
    | IncompleteSwitch of VarId * Constructor list
    | SwitchCanFail of VarId
    | NegatedGoalCanSucceed
    | NegatedGoalCanFail
    | GoalCanSucceedMoreThanOnce
    | GoalCanSucceed
    | GoalCanFail

type DeterminismmDiagnosisContext =
    | DeterminismDiagnosisContextNone
    | DeterminismDiagnosisContextCall of RelationProcId
    | DeterminismDiagnosisContextUnify of VarId * UnifyRhs * UnifyContext

type DeterminismDiagnosisInfo =
    { Diagnosis: DeterminismDiagnosis
      Context: DeterminismmDiagnosisContext
      SourceInfo: SourceInfo }

type DeterminismError =
    | CallMustBeInSingleSolutionContext of callee: RelationProcId
    | DeclarationNotSatisfied of declared: Determinism * inferred: Determinism * diagnosis: DeterminismDiagnosis list

type DeterminismWarning = DeclarationTooLax of declared: Determinism * inferred: Determinism

type DeterminismErrorInfo =
    { Error: DeterminismError
      Relation: RelationProcId
      SourceInfo: SourceInfo }

type DeterminismWarningInfo =
    { Warning: DeterminismWarning
      Relation: RelationProcId
      SourceInfo: SourceInfo }
