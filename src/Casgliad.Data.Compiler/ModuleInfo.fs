namespace Casgliad.Data.Compiler

open System.Collections.Generic

open Casgliad.Data

[<AutoOpen>]
module internal ModuleInfoModule =

    type ProcInfo =
        { ProcId: ProcId
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
        (procId: ProcId)
        (mode: RelationMode)
        =
        let sourceInfo = relationSourceInfo relAttr

        match (parseModes sourceInfo args mode) with
        | Ok modes ->
            { ProcId = procId
              SourceInfo = sourceInfo
              Modes = List.map (fun (i1, i2) -> (ofInst instTable i1, ofBoundInst instTable i2)) modes.Modes
              Determinism = mode.Determinism
              Args = args
              ProcGoal = goal
              VarSet = varset }
        | Error _ -> raise (System.Exception ("invalid modes"))

    type RelationInfo =
        { Name: RelationId
          SourceInfo: SourceInfo
          Procedures: Map<ProcId, ProcInfo> }

    let initRelation
        (instTable: InstTable)
        (moduleName: string)
        (relAttr: RelationAttribute)
        (relation: RelationBase)
        (args: VarId list)
        (goal: Goal)
        (varset: VarSet)
        =
        let sourceInfo = relationSourceInfo relAttr

        let procList =
            List.mapi (fun i -> initProc instTable relAttr args goal varset (i * 1<procIdMeasure>)) relation.Modes

        let procMap =
            List.fold (fun map (proc: ProcInfo) -> Map.add proc.ProcId proc map) Map.empty procList

        { Name =
              { ModuleName = moduleName
                RelationName = relation.Name }
          SourceInfo = sourceInfo
          Procedures = procMap }

    type ModuleInfo =
        { Relations: Dictionary<RelationId, RelationInfo>
          InstTable: InstTable }
        static member init =
            { Relations = Dictionary ()
              InstTable = InstTable () }

        member x.addRelation(relation) =
            x.Relations.[relation.Name] = relation |> ignore

        member x.processRelations(f: (RelationInfo -> ModuleInfo -> RelationInfo)) : unit =
            let processRelation (m: ModuleInfo) (r: KeyValuePair<RelationId, RelationInfo>) =
                let r' = f r.Value m

                m.Relations.[r.Key] = r' |> ignore

            x.Relations |> Seq.iter (processRelation x)
