namespace Kanren.Data.Compiler

open FSharp.Quotations
open Kanren.Data

[<AutoOpen>]
module ModuleInfoModule =

    type ProcInfo = { ProcId: int; SourceInfo: SourceInfo; Modes: Mode list; Determinism: Determinism; Args: Var list; Goal: Goal; VarSet: VarSet }

    let parseMode (sourceInfo: SourceInfo) (mode: string) =
        match mode with
            | "in" ->
                Result.Ok (Inst.Ground, Inst.Ground)
            | "out" ->
                Result.Ok (Inst.Free, Inst.Ground)
            | _ ->
                Result.Error (Error.invalidModeError sourceInfo mode)

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
