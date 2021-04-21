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
            sourceInfo: SourceInfo;
        }
        static member init sourceInfo =
            {
                nonLocals = Set.empty;
                instmapDelta = Map.empty;
                determinism = Determinism.Det;
                sourceInfo = sourceInfo;
            }

    type Constructor =
        | Constant of value: obj * constType: System.Type
        | Tuple
        | Record of System.Type
        | UnionCase of FSharp.Reflection.UnionCaseInfo

    type UnifyRhs =
        | Var of Var
        | Constructor of args: Var list * constructor: Constructor

    type GoalExpr =
        | Unify of lhs: Var * rhs : UnifyRhs
        | Call of func: System.Reflection.PropertyInfo * args: (Var list)
        | FSharpCall of func: System.Reflection.MethodInfo * returnValue: Var * args : (Var list)
        | Conj of Goal list
        | Disj of Goal list
        | Switch of var: Var * canFail: bool * cases: Case list
        | IfThenElse of condGoal: Goal * thenGoal: Goal * elseGoal: Goal * condExistVars: SetOfVar
        | Not of Goal
    and
        Goal = { goal : GoalExpr; info : GoalInfo }
    and
        Case = { constructor: Constructor; otherConstructors: Constructor list; caseGoal: Goal }

    let (|Fail|_|) goalExpr =
        match goalExpr with
        | Disj([]) ->
        Some ()
        | _ ->
            None
    
    let (|Succeed|_|) goalExpr =
        match goalExpr with
        | Conj([]) ->
        Some ()
        | _ ->
            None

    let unifyRhsVars rhs  (vars : Var Set) =
        match rhs with
            | Var(var) -> vars.Add(var)
            | Constructor(args, _) -> List.fold (flip Set.add) vars args

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
            | Switch(var, _, cases) ->
                let vars' = Set.add var vars
                List.fold (fun vars'' case -> goalVars case.caseGoal vars'') vars' cases
            | IfThenElse(condGoal, thenGoal, elseGoal, existVars) ->
                let vars' = Set.fold (flip Set.add) vars existVars
                List.fold (flip goalVars) vars [condGoal; thenGoal; elseGoal]
            | Not(negGoal) ->
                goalVars negGoal vars
    and
        goalVars (goal : Goal) vars = goalExprVars goal.goal vars

