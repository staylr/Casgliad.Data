namespace Kanren.Data.Compiler

open Kanren.Data
open FSharp.Quotations

[<AutoOpen>]
module Goal =

    type SetOfVar = Var Set

    type Instmap = Map<Var, Kanren.Data.Inst>

    type InstmapDelta = Instmap

    type GoalInfo =
        {
            nonLocals : SetOfVar;
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
        | Not of Goal
    and
        Goal = { goal : GoalExpr; info : GoalInfo }

    let unifyRhsVars rhs  (vars : Var Set) =
        match rhs with
            | Var (var) -> vars.Add(var)
            | Constant (_, _) -> vars

    let rec goalExprVars goal (vars : Var Set) =
        match goal with
            | Unify(lhs, rhs) ->
                unifyRhsVars rhs (vars.Add(lhs))
            | Call(_, args) ->
                List.fold (flip Set.add) vars args
            | FSharpCall(_, ret, args) ->
                 List.fold (flip Set.add) vars (ret :: args)
            | Conj(goals)
            | Disj(goals) ->
                List.fold (flip goalVars) vars goals
            | Not(negGoal) ->
                goalVars negGoal vars
    and
        goalVars (goal : Goal) vars = goalExprVars goal.goal vars

