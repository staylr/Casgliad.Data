namespace Kanren.Data.Compiler

open Kanren.Data
open FSharp.Quotations

[<AutoOpen>]
module Goal =
    type Inst =
        | Ground
        | Free

    type Mode = Inst * Inst

    type SetOfVar = Var Set

    type Instmap = Map<Var, Inst>

    type InstmapDelta = Instmap

    type SourceInfo = { File: string; StartLine: int; StartCol: int; EndLine: int; EndCol: int }

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
        | Call of func : System.Reflection.MethodInfo * args : (Var list)
        | FSharpCall of func : System.Reflection.MethodInfo * returnValue : Var * args : (Var list)
        | Conj of Goal list
        | Disj of Goal list
        | Not of Goal
    and
        Goal = { goal : GoalExpr; info : GoalInfo }

    type ErrorContext =
        | Goal of Goal
        | Expr of Expr
        | String of string

    type ErrorSeverity =
        | None = 0
        | Info = 1
        | Warning = 2
        | Error = 3

    let maxSeverity (x: ErrorSeverity) (y: ErrorSeverity) = if (x > y) then x else y

    type Error = { Text: string; Location: SourceInfo Option; Context: ErrorContext; Severity: ErrorSeverity}

    let maxSeverityOfList errors =
        List.fold (fun max (e1: Error) -> maxSeverity e1.Severity max) ErrorSeverity.None errors

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

    type ProcInfo = { ProcId: int; SourceInfo: SourceInfo; Modes: Mode list; Determinism: Determinism; Args: Var list; Goal: Goal; VarSet: VarSet }

    let parseMode (sourceInfo: SourceInfo) (mode: string) =
        match mode with
            | "in" ->
                Result.Ok (Inst.Ground, Inst.Ground)
            | "out" ->
                Result.Ok (Inst.Free, Inst.Ground)
            | _ ->
                Result.Error { Text = $"invalid mode {mode}"; Context = String "mode attribute";
                                Location = Some sourceInfo; Severity = ErrorSeverity.Error; }

    let parseModes (sourceInfo: SourceInfo) (args: Var list) (modeAttr: ModeAttribute) =
        if (modeAttr.Mode = "") then
            seq { for i in [1 .. List.length args] -> (Inst.Free, Inst.Ground) }
                |> List.ofSeq
                |> Ok
        else
            let splitModes = modeAttr.Mode.Split(',', System.StringSplitOptions.RemoveEmptyEntries ||| System.StringSplitOptions.TrimEntries)
                                |> List.ofArray
            let results = List.map (parseMode sourceInfo) splitModes
            combineResults results

    let initProc (args: Var list) (goal: Goal) (varset: VarSet) (procId: int) (modeAttr: ModeAttribute) =
        let sourceInfo = { File = modeAttr.SourcePath; StartLine = modeAttr.SourceLine; EndLine = modeAttr.SourceLine; StartCol = 0; EndCol = 0 }
        match (parseModes sourceInfo args modeAttr) with
            | Ok modes ->
                { ProcId = procId; SourceInfo = sourceInfo; Modes = modes; Determinism = modeAttr.Determinism; Args = args; Goal = goal; VarSet = varset }
            | Error _ ->
                raise (System.Exception("invalid modes"))

    type RelationInfo = { Name: string; SourceInfo: SourceInfo; Procedures: Map<int, ProcInfo>; }

    let relationSourceInfo (relAttr: RelationAttribute) = { File = relAttr.SourcePath; StartLine = relAttr.SourceLine; EndLine = relAttr.SourceLine; StartCol = 0; EndCol = 0 }

    let initRelation (relAttr: RelationAttribute) (modeAttrs: ModeAttribute list) (args: Var list) (goal: Goal) (varset: VarSet) =
        let sourceInfo = relationSourceInfo relAttr
        let procs = List.mapi (initProc args goal varset) modeAttrs
        let procMap = List.fold (fun map (proc : ProcInfo) -> Map.add proc.ProcId proc map) Map.empty procs
        { Name = relAttr.Name; SourceInfo = sourceInfo; Procedures = procMap }

    type ModuleInfo = { Relations: Map<string, RelationInfo> }
        with
        static member init = { Relations = Map.empty }

        member x.addRelation(relation) =
                { x with Relations = Map.add relation.Name relation x.Relations }

        member x.processRelations(f : (RelationInfo -> ModuleInfo -> RelationInfo)) =
                let processRelation(m : ModuleInfo) (_, r) =
                        let r' = f r m
                        let m' = { m with Relations = Map.add r.Name r m.Relations }
                        m'
                Map.toSeq x.Relations
                    |> Seq.fold processRelation x

