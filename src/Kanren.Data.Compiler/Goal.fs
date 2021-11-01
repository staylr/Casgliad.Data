namespace Kanren.Data.Compiler

open Kanren.Data

module GoalWriter =

    [<System.Flags>]
    type GoalToStringFlags =
        | None = 0
        | PrintInfo = 1

    type GoalToStringInfo =
        { Writer: System.CodeDom.Compiler.IndentedTextWriter
          VarSet: VarSet
          Flags: GoalToStringFlags }

    type GoalToStringFunc = GoalToStringInfo -> unit

    type GoalToStringBuilder() =
        member inline __.Yield(txt: string) =
            fun (b: GoalToStringInfo) -> b.Writer.Write txt |> ignore

        member inline __.Yield(c: char) =
            fun (b: GoalToStringInfo) -> b.Writer.Write c |> ignore

        member inline __.Yield(v: VarId) =
            fun (b: GoalToStringInfo) ->
                let var = b.VarSet.[v]
                b.Writer.Write var.Name |> ignore

        member inline __.Yield(vs: VarId list) =
            fun (b: GoalToStringInfo) ->
                match vs with
                | v :: vs' ->
                    b |> __.Yield ("(")
                    b |> __.Yield (v)

                    for v' in vs' do
                        b |> __.Yield (", ")
                        b |> __.Yield (v')

                    b |> __.Yield (')')
                | _ -> b |> __.Yield (')')

        member inline __.Yield(strings: #seq<string>) =
            fun (b: GoalToStringInfo) ->
                for s in strings do
                    s |> b.Writer.WriteLine |> ignore

        member inline __.YieldFrom(f: GoalToStringFunc) = f

        member __.Combine(f, g) =
            fun (b: GoalToStringInfo) ->
                f b
                g b

        member __.Delay f = fun (b: GoalToStringInfo) -> (f ()) b
        member __.Zero() = ignore

        member __.For(xs: 'a seq, f: 'a -> GoalToStringFunc) =
            fun (b: GoalToStringInfo) ->
                let e = xs.GetEnumerator ()

                while e.MoveNext () do
                    (f e.Current) b

        member __.While(p: unit -> bool, f: GoalToStringFunc) =
            fun (b: GoalToStringInfo) ->
                while p () do
                    f b

        member __.Run(f: GoalToStringFunc) = f

    let gts = new GoalToStringBuilder ()

    let indent (f: GoalToStringFunc) (info: GoalToStringInfo) =
        do info.Writer.Indent <- info.Writer.Indent + 4
        do info.Writer.WriteLine ()
        do f info
        do info.Writer.Indent <- info.Writer.Indent - 4
        do info.Writer.WriteLine ()
        ()

    let rec listToString l f (sep: string) =
        gts {
            match l with
            | x :: xs ->
                yield! f x

                match xs with
                | _ :: _ -> yield sep
                | [] -> yield! listToString xs f sep
            | [] -> ()
        }

[<AutoOpen>]
module Goal =

    open GoalWriter

    let emptySetOfVar = TagSet.empty<varIdMeasure>

    type InstMap =
        private
        | Reachable of Map<VarId, BoundInstE>
        | Unreachable
        static member initReachable = Reachable (Map.empty)
        static member initUnreachable = Unreachable
        member this.isReachable () = this <> Unreachable

        member this.lookupVar v =
            match this with
            | Reachable m ->
                match m.TryGetValue (v) with
                | true, inst -> InstE.Bound inst
                | _ -> InstE.Free
            | Unreachable -> InstE.Bound BoundInstE.NotReached

        member this.setVarBound v inst =
            match this with
            | Reachable m -> m.Add (v, inst) |> Reachable
            | Unreachable -> this

        member this.setVar v inst =
            match inst with
            | InstE.Free -> this
            | InstE.Bound boundInst -> this.setVarBound v boundInst

        member this.restrict vars =
            match this with
            | Reachable m ->
                Map.filter (fun v _ -> TagSet.contains v vars) m
                |> Reachable
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

                    nonLocals
                    |> TagSet.fold addVarToInstMapDelta Map.empty
                    |> Reachable

    type InstMapDelta = InstMap

    type RelationId = { ModuleName: string; RelationName: string }
        with
        override this.ToString() = $"{this.ModuleName}.{this.RelationName}"

    [<Measure>]
    type procIdMeasure

    // The ID of a specific mode for a relation.
    type ProcId = int<procIdMeasure>

    let invalidProcId = -1<procIdMeasure>

    type RelationProcId = RelationId * ProcId

    type FSharpProcId = System.Reflection.MethodInfo * ProcId

    type GoalInfo =
        { NonLocals: SetOfVar
          InstMapDelta: InstMapDelta
          Determinism: Determinism
          SourceInfo: SourceInfo }
        static member init sourceInfo =
            { NonLocals = TagSet.empty<varIdMeasure>
              InstMapDelta = Unreachable
              Determinism = Determinism.Det
              SourceInfo = sourceInfo }

    type VarVarUnifyType =
        | Assign
        | Test

    type VarCtorUnifyType =
        | Construct
        | Deconstruct

    type UnifyMode = ModeE * ModeE

    type UnifyMainContext =
        | ExplicitUnify
        | HeadUnify of ArgIndex: int
        | CallArgUnify of Name: RelationId * ArgIndex: int
        | FSharpCallArgUnify of Callee: System.Reflection.MethodInfo * ArgIndex: int
        | HigherOrderCallArgUnify of ArgIndex: int
        | ImplicitUnify

    type UnifySubContextFunctor =
        | FunctorConstructor of Constructor
        | FunctorCall of System.Reflection.MethodInfo

    type UnifySubContext =
        { Functor: UnifySubContextFunctor
          ArgIndex: int }

    type UnifyContext =
        { MainContext: UnifyMainContext
          SubContext: UnifySubContext list }

    let initUnifyContext mainContext =
        { MainContext = mainContext
          SubContext = [] }

    type GoalExpr =
        | Unify of lhs: VarId * rhs: UnifyRhs * mode: UnifyMode * context: UnifyContext

        // A call to a Kanren relation.
        | Call of relationId: RelationProcId * args: (VarId list)

        // A call to a F# function.
        | FSharpCall of
            // The called function.
            func: FSharpProcId *
            // The return value. This will be `None' if the call is used as a goal e.g. x < y
            returnValue: VarId option *
            // Function arguments.
            args: (VarId list)
        | Conj of Goal list
        | Disj of Goal list
        | Switch of var: VarId * canFail: bool * cases: Case list
        | IfThenElse of condGoal: Goal * thenGoal: Goal * elseGoal: Goal
        | Not of Goal
        member x.Dump() : GoalToStringFunc =
            gts {
                match x with
                | Unify (lhs, rhs, _, _) ->
                    yield lhs
                    yield " = "
                    yield! rhs.Dump ()
                | Call (callee, args) ->
                    yield callee.ToString()
                    yield args
                | FSharpCall (method, returnValue, args) ->
                    yield returnValue.ToString()
                    yield " = F#"
                    yield (fst method).Name
                    yield args
                | Conj (goals) -> yield! indent (listToString goals (fun goal -> goal.Dump ()) ",\n")
                | Disj (goals) ->
                    yield "("
                    yield! indent (listToString goals (fun goal -> goal.Dump ()) ";\n")
                | Switch (var, canFail, cases) -> yield ""
                | IfThenElse (condGoal, thenGoal, elseGoal) -> yield ""
                | Not (negGoal) ->
                    yield " not ("
                    yield! indent (negGoal.Dump ())
                    yield ")"
            }

    and Goal =
        { Goal: GoalExpr
          Info: GoalInfo }
        member x.Dump() = gts { yield! x.Goal.Dump () }

    and Case =
        { Constructor: Constructor
          OtherConstructors: Constructor list
          CaseGoal: Goal }

    and UnifyRhs =
        | Var of Var: VarId * UnifyType: VarVarUnifyType
        | Constructor of
            Constructor: Constructor *
            Args: VarId list *
            UnifyType: VarCtorUnifyType *
            ArgModes: ModeE list *
            CanFail: CanFail
        | Lambda of NonLocals: VarId list * Args: VarId list * Modes: Mode list * Detism: Determinism * Goal: Goal
        member x.Dump() : GoalToStringFunc =
            gts {
                match x with
                | Var (v, _) -> yield v
                | Constructor (ctor, args, _, _, _) ->
                    yield ctor.ToString ()

                    match args with
                    | _ :: _ -> yield args
                    | [] -> yield ""
                | Lambda (_, _, _, _, _) -> yield ("lambda")
            }

    let (|Fail|_|) goalExpr =
        match goalExpr with
        | Disj ([]) -> Some ()
        | _ -> None

    let (|Succeed|_|) goalExpr =
        match goalExpr with
        | Conj ([]) -> Some ()
        | _ -> None

    let rec goalExprVars goal (vars: SetOfVar) =
        match goal with
        | Unify (lhs, rhs, _, _) -> unifyRhsVars rhs (TagSet.add lhs vars)
        | Call (_, args) -> List.fold (flip TagSet.add) vars args
        | FSharpCall (_, ret, args) -> List.fold (flip TagSet.add) vars (consOption ret args)
        | Conj (goals)
        | Disj (goals) -> List.fold (flip goalVars) vars goals
        | Switch (var, _, cases) ->
            let vars' = TagSet.add var vars
            List.fold (fun vars'' case -> goalVars case.CaseGoal vars'') vars' cases
        | IfThenElse (condGoal, thenGoal, elseGoal) -> List.fold (flip goalVars) vars [ condGoal; thenGoal; elseGoal ]
        | Not (negGoal) -> goalVars negGoal vars

    and goalVars (goal: Goal) vars = goalExprVars goal.Goal vars

    and unifyRhsVars rhs (vars: SetOfVar) =
        match rhs with
        | Var (var, _) -> TagSet.add var vars
        | Constructor (_, args, _, _, _) -> List.fold (flip TagSet.add) vars args
        | Lambda (nonLocals, args, _, _, goal) ->
            TagSet.union vars (TagSet.union (TagSet.ofList nonLocals) (TagSet.ofList args))
            |> goalVars goal
