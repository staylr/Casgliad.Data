namespace Kanren.Data.Compiler

open Kanren.Data
open FSharp.Quotations

[<AutoOpen>]
module Goal =

    type VarSet = Var Set

    type Inst =
        | Ground
        | Free

    type Instmap = Map<Var, Inst>

    type InstmapDelta = Instmap

    type SourceInfo = { File: string; StartLine: int; StartCol: int; EndLine: int; EndCol: int }

    type GoalInfo =
        {
            varSet : VarSet;
            nonLocals : VarSet;
            instmapDelta: InstmapDelta;
            determinism: Determinism;
            sourceInfo: SourceInfo Option;
        }
        static member init sourceInfo =
            {
                varSet = Set.empty;
                nonLocals = Set.empty;
                instmapDelta = Map.empty;
                determinism = Determinism.Det;
                sourceInfo = sourceInfo;
            }

    type GoalExpr =
        | Unify of lhs : Expr * rhs : Expr * utype: System.Type
        | Call of func : System.Reflection.PropertyInfo * args : (Expr list)
        | Conj of Goal list
        | Disj of Goal list
        | Exists of var : Var * goal : Goal
        | Not of Goal
    and
        Goal = { goal : GoalExpr; info : GoalInfo }
