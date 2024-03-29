[<AutoOpen>]
module internal Casgliad.Data.Compiler.InstMap

open Casgliad.Data.Compiler.InstMatch

type private InstMapping = Map<VarId, BoundInstE>

type InstMap =
    private
    | Reachable of InstMapping
    | Unreachable

    static member initReachable = Reachable(Map.empty)
    static member initUnreachable = Unreachable
    member this.isReachable() = this <> Unreachable

    member this.lookupVar v =
        match this with
        | Reachable m ->
            match m.TryGetValue(v) with
            | true, inst -> InstE.Bound inst
            | _ -> InstE.Free
        | Unreachable -> InstE.Bound BoundInstE.NotReached

    member this.mappings() =
        match this with
        | Reachable m -> m
        | Unreachable -> Map.empty

    member this.setVarBound v inst =
        match this with
        | Reachable m -> m.Add(v, inst) |> Reachable
        | Unreachable -> this

    member this.setVar v inst =
        match inst with
        | InstE.Free -> this
        | InstE.Bound boundInst -> this.setVarBound v boundInst

    member this.restrict vars =
        match this with
        | Reachable m -> Map.filter (fun v _ -> TagSet.contains v vars) m |> Reachable
        | Unreachable -> Unreachable

    member this.hasOutputVars (instTable: InstTable) (varSet: VarSet) (instMap0: InstMap) (nonLocals: SetOfVar) =
        match this with
        | Unreachable -> true
        | Reachable m ->
            let varIsOutput var =
                let oldInst = instMap0.lookupVar var

                match m.TryFind var with
                | Some newInst ->
                    let progVar = varSet.[var]

                    instMatchesBinding instTable (Bound newInst) oldInst (Some progVar.VarType) AnyMatchesAny
                    || instTable.instContainsAny (oldInst)

                | None -> false

            nonLocals |> TagSet.exists varIsOutput

    member this.applyInstMapDelta(delta: InstMap) : InstMap =
        match this with
        | Reachable m ->
            match delta with
            | Reachable deltaM -> deltaM |> Map.fold (fun (m': InstMapping) k v -> m'.Add(k, v)) m |> Reachable
            | Unreachable -> Unreachable
        | Unreachable -> Unreachable

    member this.renameVars(substitution: Map<VarId, VarId>, mustRename: bool) : InstMap =
        match this with
        | Reachable m ->
            let renameElement (rm: InstMapping) (v1: VarId) (inst: BoundInstE) =
                Map.add (applyRenaming substitution mustRename v1) inst rm

            Map.fold renameElement Map.empty m |> Reachable
        | Unreachable -> Unreachable

    static member computeInstMapDelta instMapA instMapB nonLocals =
        match instMapA with
        | Unreachable -> Unreachable
        | Reachable mA ->
            match instMapB with
            | Unreachable -> Unreachable
            | Reachable mB ->
                let addVarToInstMapDelta instMapDelta v =
                    let instA = instMapA.lookupVar v
                    let instB = instMapB.lookupVar v

                    if (instA = instB) then
                        instMapDelta
                    else
                        match instB with
                        | InstE.Bound boundInstB -> Map.add v boundInstB instMapDelta
                        | InstE.Free -> instMapDelta

                nonLocals |> TagSet.fold addVarToInstMapDelta Map.empty |> Reachable

    static member ofInitialArgModes args argModes =
        List.fold2
            (fun (instMap': InstMap) arg (initialInst, _) -> instMap'.setVar arg initialInst)
            InstMap.initReachable
            args
            argModes

type InstMapDelta = InstMap
