namespace Casgliad.Data.Compiler

open System.Collections.Generic


open Casgliad.Data
open Casgliad.Data.Compiler

[<AutoOpen>]
module internal ModuleInfoModule =

    type ProcInfo =
        { ProcId: ProcId
          SourceInfo: SourceInfo
          Modes: (InstE * BoundInstE) list
          Determinism: Determinism
          InferredDeterminism: Determinism option
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

    let initProcFromSource
        (instTable: InstTable)
        (sourceInfo: SourceInfo)
        (args: VarId list)
        (goal: Goal)
        (varset: VarSet)
        (procId: ProcId)
        (mode: RelationMode)
        =
        match (parseModes sourceInfo args mode) with
        | Ok modes ->
            { ProcId = procId
              SourceInfo = sourceInfo
              Modes = List.map (fun (i1, i2) -> (ofInst instTable i1, ofBoundInst instTable i2)) modes.Modes
              Determinism = mode.Determinism
              InferredDeterminism = None
              Args = args
              ProcGoal = goal
              VarSet = varset }
        | Error _ -> raise (System.Exception("invalid modes"))

    let initProc
        (sourceInfo: SourceInfo)
        (args: VarId list)
        (goal: Goal)
        (varset: VarSet)
        (procId: ProcId)
        (modes: RelationModeE)
        =
        { ProcId = procId
          SourceInfo = sourceInfo
          Modes = modes.Modes
          Determinism = modes.Determinism
          InferredDeterminism = None
          Args = args
          ProcGoal = goal
          VarSet = varset }

    type RelationInfo =
        { Name: RelationId
          SourceInfo: SourceInfo
          Procedures: Map<ProcId, ProcInfo> }

    let initRelation
        (instTable: InstTable)
        (moduleName: string)
        (sourceInfo: SourceInfo)
        (relation: RelationBase)
        (args: VarId list)
        (goal: Goal)
        (varset: VarSet)
        =
        let procList =
            List.mapi
                (fun i -> initProcFromSource instTable sourceInfo args goal varset (i * 1<procIdMeasure>))
                relation.Modes

        let procMap =
            List.fold (fun map (proc: ProcInfo) -> Map.add proc.ProcId proc map) Map.empty procList

        { Name =
            { ModuleName = moduleName
              RelationName = UserRelation relation.Name }
          SourceInfo = sourceInfo
          Procedures = procMap }

    let relationOfGoal (name: RelationId) (goal: Goal) (args: VarId list) (instMap0: InstMap) (varSet: VarSet) =
        let instMap = instMap0.applyInstMapDelta (goal.Info.InstMapDelta)

        let getArgMode arg =
            let inst0 = instMap0.lookupVar (arg)
            let inst = instMap.lookupVar (arg)

            match inst with
            | Free -> invalidOp $"unexpected unbound argument {arg}"
            | Bound boundInst -> (inst0, boundInst)

        let modes = List.map getArgMode args

        let procId = 0<procIdMeasure>

        let proc =
            initProc
                goal.Info.SourceInfo
                args
                goal
                varSet
                procId
                { Modes = modes
                  Determinism = goal.Info.Determinism }

        let newRelation =
            { Name = name
              SourceInfo = goal.Info.SourceInfo
              Procedures = seq { proc.ProcId, proc } |> Map.ofSeq }

        let goal =
            { Goal = Call((newRelation.Name, procId), args)
              Info = goal.Info }

        (newRelation, goal)


    type StronglyConnectedComponent =
        { Number: int
          Members: RelationProcId list
          EntryPoints: RelationProcId list }

    // Mutable maps to avoid threading this everywhere.
    type ModuleInfo =
        { Relations: Dictionary<RelationId, RelationInfo>
          InstTable: InstTable }

        static member init =
            { Relations = Dictionary()
              InstTable = InstTable() }

        member this.addRelation(relation) =
            this.Relations.Add(relation.Name, relation)

        member this.processRelations(f: (RelationInfo -> ModuleInfo -> RelationInfo)) : unit =
            let processRelation (m: ModuleInfo) (r: KeyValuePair<RelationId, RelationInfo>) =
                let r' = f r.Value m

                m.Relations.[r.Key] <- r'

            this.Relations |> Seq.iter (processRelation this)

        member this.processProcedures
            (f: (RelationProcId -> RelationInfo -> ProcInfo -> ModuleInfo -> ProcInfo))
            : unit =
            let processRelationProcedures (relationInfo: RelationInfo) (m: ModuleInfo) =
                let procs' =
                    relationInfo.Procedures
                    |> Map.map (fun procId procInfo -> f (relationInfo.Name, procId) relationInfo procInfo m)

                { relationInfo with
                    Procedures = procs' }

            this.processRelations (processRelationProcedures)

        member this.getRelation(relationId: RelationId) = this.Relations.[relationId]

        member this.getRelationProcInfo(relationProcId: RelationProcId) =
            let relation = this.getRelation (fst relationProcId)
            let proc = relation.Procedures.[snd relationProcId]
            (relation, proc)

        member this.setRelationProcInfo
            (
                relationProcId: RelationProcId,
                relationInfo: RelationInfo,
                procInfo: ProcInfo
            ) =
            relationInfo.Procedures[snd relationProcId] = procInfo

        member x.StronglyConnectedComponents() : StronglyConnectedComponent seq =
            let goalCallee (callees: Set<RelationProcId>) goal =
                match goal.Goal with
                | Call(callee, _) -> callees.Add callee
                | _ -> callees

            let graph =
                QuikGraph.BidirectionalGraph<RelationProcId, QuikGraph.Edge<RelationProcId>>()

            x.Relations
            |> Seq.iter (fun r ->
                r.Value.Procedures
                |> Seq.iter (fun p -> graph.AddVertex(r.Key, p.Key) |> ignore))

            x.Relations
            |> Seq.iter (fun r ->
                r.Value.Procedures
                |> Seq.iter (fun p ->
                    p.Value.ProcGoal
                    |> goalFold goalCallee Set.empty
                    |> Set.iter (fun callee -> graph.AddEdge(QuikGraph.Edge((r.Key, p.Key), callee)) |> ignore)))

            let components = Dictionary<RelationProcId, int>()

            QuikGraph.Algorithms.AlgorithmExtensions.StronglyConnectedComponents(graph, components)
            |> ignore

            // Convert to lists of procedures.
            components
            |> Seq.groupBy (fun kv -> kv.Value)
            |> Seq.map (fun (comp, vertices) -> comp, vertices |> Seq.map (fun kv -> kv.Key))
            |> Seq.map (fun (comp, vertices) ->
                { Number = comp
                  Members = List.ofSeq vertices
                  EntryPoints =
                    vertices
                    |> Seq.filter (fun v ->
                        graph.InEdges(v) |> Seq.exists (fun e -> not (Seq.contains e.Source vertices)))
                    |> List.ofSeq })
