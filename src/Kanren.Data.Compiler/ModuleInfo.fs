namespace Kanren.Data.Compiler

open Kanren.Data

[<AutoOpen>]
module ModuleInfoModule =

    type ProcInfo =
        { ProcId: int
          SourceInfo: SourceInfo
          Modes: (InstE * BoundInstE) list
          Determinism: Determinism
          Args: VarId list
          ProcGoal: Goal
          VarSet: VarSet }

    let parseModes (sourceInfo: SourceInfo) (args: VarId list) (modes: RelationMode) =
        if (args.Length = modes.Modes.Length) then
            Ok modes
        else
            Error [ (Error.invalidModeListLengthError sourceInfo modes.Modes.Length args.Length) ]

    let relationSourceInfo (relAttr: RelationAttribute) =
        { File = relAttr.SourcePath
          StartLine = relAttr.SourceLine
          EndLine = relAttr.SourceLine
          StartCol = 0
          EndCol = 0 }

    let initProc
        (instTable: InstTable)
        (relAttr: RelationAttribute)
        (args: VarId list)
        (goal: Goal)
        (varset: VarSet)
        (procId: int)
        (mode: RelationMode)
        =
        let sourceInfo = relationSourceInfo relAttr

        match (parseModes sourceInfo args mode) with
        | Ok modes ->
            { ProcId = procId
              SourceInfo = sourceInfo
              Modes = List.map (fun (i1, i2) -> (ofInst instTable i1, ofBoundInst instTable i2)) mode.Modes
              Determinism = mode.Determinism
              Args = args
              ProcGoal = goal
              VarSet = varset }
        | Error _ -> raise (System.Exception("invalid modes"))

    type RelationInfo =
        { Name: string
          SourceInfo: SourceInfo
          Procedures: Map<int, ProcInfo> }

    let initRelation
        (instTable: InstTable)
        (relAttr: RelationAttribute)
        (relation: RelationBase)
        (args: VarId list)
        (goal: Goal)
        (varset: VarSet)
        =
        let sourceInfo = relationSourceInfo relAttr

        let procs =
            List.mapi (initProc instTable relAttr args goal varset) relation.Modes

        let procMap =
            List.fold (fun map (proc: ProcInfo) -> Map.add proc.ProcId proc map) Map.empty procs

        { Name = relation.Name
          SourceInfo = sourceInfo
          Procedures = procMap }

    type ModuleInfo =
        { Relations: Map<string, RelationInfo>
          InstTable: InstTable }
        static member init = { Relations = Map.empty; InstTable = InstTable() }

        member x.addRelation(relation) =
            { x with
                  Relations = Map.add relation.Name relation x.Relations }

        member x.processRelations(f: (RelationInfo -> ModuleInfo -> RelationInfo)) =
            let processRelation (m: ModuleInfo) (_, r) =
                let r' = f r m

                let m' =
                    { m with
                          Relations = Map.add r.Name r m.Relations }

                m'

            Map.toSeq x.Relations
            |> Seq.fold processRelation x
