namespace Kanren.Data.Compiler

open Kanren.Data
open FSharp.Quotations

[<AutoOpen>]
module Goal =
    type Inst =
        | Ground
        | Free

    type Instmap = Map<Var, Inst>

    type InstmapDelta = Instmap

    type SourceInfo = { File: string; StartLine: int; StartCol: int; EndLine: int; EndCol: int }

    type GoalInfo =
        {
            nonLocals : Set<Var>;
            instmapDelta: InstmapDelta;
            determinism: Determinism;
            sourceInfo: SourceInfo Option;
        }
        static member init sourceInfo =
            {
                nonLocals = Set.empty;
                instmapDelta = Map.empty;
                determinism = Determinism.Det;
                sourceInfo = sourceInfo;
            }

    type UnifyRhs =
        | Var of Var
        | Constant of value : obj * constType : System.Type

    type GoalExpr =
        | Unify of lhs : Var * rhs : UnifyRhs
        | Call of func : System.Reflection.PropertyInfo * args : (Var list)
        | FSharpCall of func : System.Reflection.MethodInfo * returnValue : Var * args : (Var list)
        | Conj of Goal list
        | Disj of Goal list
        | Exists of var : Var * goal : Goal
        | Not of Goal
    and
        Goal = { goal : GoalExpr; info : GoalInfo }

    type ErrorContext =
        | Goal of Goal
        | Expr of Expr

    type Error = { Text: string; Location: SourceInfo Option; Context: ErrorContext }
