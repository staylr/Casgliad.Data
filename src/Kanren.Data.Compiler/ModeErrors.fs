namespace Kanren.Data.Compiler

open Kanren.Data

module ModeErrors =
    type ModeContext =
    | ModeContextCall of Name: string * ArgNumber: int
    | ModeContextHigherOrderCall of ArgNumber: int
    | ModeContextUnify of UnifyContext: UnifyContext
    | ModeContextUninitialized

    type VarLockReason =
    | VarLockNegation
    | VarLockIfThenElse
    | VarLockLambda
    | VarLockAtomicGoal

    type ModeErrorUnifyRhs =
    | ErrorAtVar of Var: VarId
    | ErrorAtFunctor of Ctor: Constructor * Args: VarId list
    | ErrorAtLambda of Args: VarId list // * FromToInsts list

    type VarMultiModeError =
    | NoMatchingMode of Args: VarId list
    | MoreThanOneMatchingMode of Args: VarId list
    | SomeHigherOrderArgsNonGround of Args: VarId list

    type RelationMultiModeError = { Relation: RelationInfo; Error: VarMultiModeError }

    type MergeError = { Var: VarId; Insts: (SourceInfo * Inst) list}

    type MergeContext =
    | MergeDisjunction
    | MergeIfThenElse

    type FinalInstError =
    | TooInstantiated
    | NotInstantiatedEnough
    | WronglyInstantiated

    type ModeError =
    | ModeErrorUnifyVarVar of LVar: VarId * RVar: VarId * LInst: Inst * RInst: Inst
    | ModeErrorUnifyVarFunctor of LVar: VarId * Ctor: Constructor * Args: VarId list * VarInst: Inst * ArgInsts: Inst list
    | ModeErrorUnifyVarLambda of LVar: VarId * Inst1: Inst * Inst2: Inst
    | ModeErrorHigherOrderUnify of LVar: VarId
    | ModeErrorNotSufficientlyInstantiated of Var: VarId * VarInst: Inst * ExpectedInst: Inst
    | ModeErrorNoMatchingMode of Args: VarId list * ArgInsts: Inst list * ExpectedArgInsts: Inst list list
    | ModeErrorUnschedulableConjuncts of DelayedGoal list
    | ModeErrorMergeDisjunction of MergeContext: MergeContext * MergeErrors: MergeError list
    | ModeErrorBindLockedVar of Reason: VarLockReason * Var: VarId * InitialInst: Inst * FinalInst: Inst
    | ModeErrorUnexpectedFinalInst of ArgNum: int * Var: VarId * ActualInst: Inst * ExpectedInst: Inst * Error: FinalInstError
    and ModeErrorInfo = { Vars: SetOfVar; Error: ModeError; SourceInfo: SourceInfo; ModeContext: ModeContext }
    and DelayedGoal = { Vars: SetOfVar; ErrorInfo: ModeErrorInfo; Goal: Goal }

    type ModeWarning =
    | CannotSucceedVarVar of LVar: VarId * RVar: VarId * LInst: Inst * RInst: Inst
    | CannotSucceedVarFunctor of LVar: VarId * Inst: Inst * Ctor: Constructor
    | CannotSucceedGroundOccurCheck of LVar: VarId * Ctor: Constructor

    type ModeWarningInfo = { Warning: ModeWarning; SourceInfo: SourceInfo; ModeContext: ModeContext }
