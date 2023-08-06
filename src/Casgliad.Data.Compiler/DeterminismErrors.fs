module internal Casgliad.Data.Compiler.DeterminismErrors

open Casgliad.Data

type DeterminismDiagnosis =
    | DiagnosisDisjunctionHasMultipleClausesWithSolutions
    | DiagnosisIncompleteSwitch of VarId * Constructor list
    | DiagnosisSwitchCanFail of VarId
    | DiagnosisNegatedGoalCanSucceed
    | DiagnosisNegatedGoalCanFail
    | DiagnosisGoalCanSucceedMoreThanOnce
    | DiagnosisGoalCanSucceed
    | DiagnosisGoalCanFail
    | DiagnosisUnknown of desired: Determinism * actual: Determinism

type DeterminismmDiagnosisContext =
    | DeterminismDiagnosisContextNone
    | DeterminismDiagnosisContextCall of RelationProcId * VarId list
    | DeterminismDiagnosisContextFSharpCall of FSharpProcId * VarId list
    | DeterminismDiagnosisContextUnify of VarId * UnifyRhs * UnifyContext

type DeterminismSwitchMatch =
    { MatchConstructor: Constructor
      MatchArgs: (VarId list) option }

type DeterminismSwitchContext =
    { SwitchVar: VarId
      FirstMatch: DeterminismSwitchMatch
      OtherMatches: DeterminismSwitchMatch list }

type DeterminismDiagnosisInfo =
    { Diagnosis: DeterminismDiagnosis
      SwitchContext: DeterminismSwitchContext list
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
