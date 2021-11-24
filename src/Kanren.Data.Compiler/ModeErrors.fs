namespace Kanren.Data.Compiler

open Kanren.Data

module internal ModeErrors =

    type ModeContext =
        | ModeContextCall of Callee: Callee * ArgNumber: int
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

    type RelationMultiModeError =
        { Relation: RelationInfo
          Error: VarMultiModeError }

    type MergeError =
        { Var: VarId
          Insts: (SourceInfo * InstE) list }

    type MergeContext =
        | MergeDisjunction
        | MergeIfThenElse

    type FinalInstError =
        | TooInstantiated
        | NotInstantiatedEnough
        | WronglyInstantiated

    type ModeError =
        | ModeErrorUnifyVarVar of LVar: VarId * RVar: VarId * LInst: InstE * RInst: InstE
        | ModeErrorUnifyVarFunctor of
            LVar: VarId *
            Ctor: Constructor *
            Args: VarId list *
            VarInst: InstE *
            ArgInsts: InstE list
        | ModeErrorUnifyVarLambda of LVar: VarId * Inst1: InstE * Inst2: InstE
        | ModeErrorHigherOrderUnify of LVar: VarId
        | ModeErrorNotSufficientlyInstantiated of Var: VarId * VarInst: InstE * ExpectedInst: InstE
        | ModeErrorNoMatchingMode of Args: VarId list * ArgInsts: InstE list * ExpectedArgInsts: InstE list list
        | ModeErrorUnschedulableConjuncts of DelayedGoal list
        | ModeErrorMergeDisjunction of MergeContext: MergeContext * MergeErrors: MergeError list
        | ModeErrorBindLockedVar of Reason: VarLockReason * Var: VarId * InitialInst: InstE * FinalInst: InstE
        | ModeErrorUnexpectedFinalInst of
            ArgNum: int *
            Var: VarId *
            ActualInst: InstE *
            ExpectedInst: InstE *
            Error: FinalInstError

    and ModeErrorInfo =
        { Vars: SetOfVar
          Error: ModeError
          SourceInfo: SourceInfo
          ModeContext: ModeContext }

    and DelayedGoal =
        { Vars: SetOfVar
          ErrorInfo: ModeErrorInfo
          Goal: Goal }

    type ModeWarning =
        | CannotSucceedVarVar of LVar: VarId * RVar: VarId * LInst: InstE * RInst: InstE
        | CannotSucceedVarFunctor of LVar: VarId * Inst: InstE * Ctor: Constructor
        | CannotSucceedGroundOccurCheck of LVar: VarId * Ctor: Constructor

    type ModeWarningInfo =
        { Warning: ModeWarning
          SourceInfo: SourceInfo
          ModeContext: ModeContext }
