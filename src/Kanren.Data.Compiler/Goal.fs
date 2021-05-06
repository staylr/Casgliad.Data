namespace Kanren.Data.Compiler

open Kanren.Data

[<AutoOpen>]
module Goal =

    type SetOfVar = VarId Set

    type Instmap = Map<VarId, Kanren.Data.Inst>

    type InstmapDelta = Instmap

    type GoalToStringFlags =
    | NoPrintInfo

    type GoalToStringFlagsSet = GoalToStringFlags Set

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
        | Var of VarId
        | Constructor of args: VarId list * constructor: Constructor

    type GoalExpr =
        | Unify of lhs: VarId * rhs : UnifyRhs
        | Call of func: System.Reflection.PropertyInfo * args: (VarId list)
        | FSharpCall of func: System.Reflection.MethodInfo * returnValue: VarId * args : (VarId list)
        | Conj of Goal list
        | Disj of Goal list
        | Switch of var: VarId * canFail: bool * cases: Case list
        | IfThenElse of condGoal: Goal * thenGoal: Goal * elseGoal: Goal * condExistVars: SetOfVar
        | Not of Goal
        with
        member x.ToString(varset: VarSet, flags: GoalToStringFlagsSet) : StringBuffer =
            stringBuffer {
                yield ""
                yield "a"
            }
    and
        Goal = { goal : GoalExpr; info : GoalInfo }
        with
        member x.ToString(varset: VarSet, flags: GoalToStringFlagsSet) =
            stringBuffer { yield! x.goal.ToString(varset, flags) }
            

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

    let unifyRhsVars rhs  (vars : SetOfVar) =
        match rhs with
            | Var(var) -> vars.Add(var)
            | Constructor(args, _) -> List.fold (flip Set.add) vars args

    let rec goalExprVars goal (vars : SetOfVar) =
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

