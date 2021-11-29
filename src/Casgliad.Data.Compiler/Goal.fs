namespace Casgliad.Data.Compiler

open Casgliad.Data

module internal GoalWriter =

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
module internal Goal =

    open GoalWriter

    let emptySetOfVar = TagSet.empty<varIdMeasure>

    type RelationId =
        { ModuleName: string
          RelationName: string }
        override this.ToString() =
            $"{this.ModuleName}.{this.RelationName}"

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
              InstMapDelta = InstMap.initUnreachable
              Determinism = Determinism.Det
              SourceInfo = sourceInfo }

    type VarVarUnifyType =
        | Assign
        | Test

    type VarCtorUnifyType =
        | Construct
        | Deconstruct

    type UnifyMode = ModeE * ModeE

    type Callee =
        | RelationCallee of Name: RelationId
        | FSharpCallee of System.Reflection.MethodInfo
        | HigherOrderCallee

    type UnifyMainContext =
        | ExplicitUnify
        | HeadUnify of ArgIndex: int
        | CallArgUnify of Callee: Callee * ArgIndex: int
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

    type ScopeReason =
        // Require the wrapped sub-goal to have the specified determinism.
        // If it does not, report an error.
        //| RequireDeterminism of Determinism

        // This scope exists to delimit a piece of code
        // with at_most_many solutions but with no outputs,
        // whose overall determinism is thus at_most_one,
        // or a piece of code that cannot succeed but some of whose
        // components are at_most_many (regardless of the number of
        // outputs).
        | Commit

        // The scope exists to prevent other compiler passes from
        // arbitrarily moving computations in or out of the scope.
        // This kind of scope can only be introduced by program
        // transformations.
        //
        // The argument says whether other compiler passes are allowed
        // to delete the scope.
        //
        // A non-removable explicit quantification may be introduced
        // to keep related goals together where optimizations that
        // separate the goals can only result in worse behaviour.
        //
        // A barrier says nothing about the determinism of either
        // the inner or the outer goal, or about pruning.
        | Barrier of removable: bool

    type GoalExpr =
        | Unify of lhs: VarId * rhs: UnifyRhs * mode: UnifyMode * context: UnifyContext

        // A call to a Casgliad relation.
        | Call of relationId: RelationProcId * args: (VarId list)

        // A call to a F# function.
        | FSharpCall of
            // The called function.
            func: FSharpProcId *
            // The return value. This will be `None' if the call is used as a goal e.g. x < y
            returnValue: VarId option *
            // Function arguments.
            args: (VarId list)
        | Conjunction of Goal list
        | Disjunction of Goal list
        | Switch of var: VarId * canFail: bool * cases: Case list
        | IfThenElse of condGoal: Goal * thenGoal: Goal * elseGoal: Goal
        | Not of Goal
        | Scope of ScopeReason * Goal
        member x.Dump() : GoalToStringFunc =
            gts {
                match x with
                | Unify (lhs, rhs, _, _) ->
                    yield lhs
                    yield " = "
                    yield! rhs.Dump ()
                | Call (callee, args) ->
                    yield callee.ToString ()
                    yield args
                | FSharpCall (method, returnValue, args) ->
                    yield returnValue.ToString ()
                    yield " = F#"
                    yield (fst method).Name
                    yield args
                | Conjunction (goals) -> yield! indent (listToString goals (fun goal -> goal.Dump ()) ",\n")
                | Disjunction (goals) ->
                    yield "("
                    yield! indent (listToString goals (fun goal -> goal.Dump ()) ";\n")
                | Switch (var, canFail, cases) -> yield ""
                | IfThenElse (condGoal, thenGoal, elseGoal) -> yield ""
                | Not (negGoal) ->
                    yield " not ("
                    yield! indent (negGoal.Dump ())
                    yield ")"
                | Scope _ -> yield ""
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
        | Disjunction ([]) -> Some ()
        | _ -> None

    let (|Succeed|_|) goalExpr =
        match goalExpr with
        | Conjunction ([]) -> Some ()
        | _ -> None

    let succeedGoal =
        { Goal.Goal = Conjunction ([])
          Info = GoalInfo.init SourceInfo.empty }

    let rec goalExprVars goal (vars: SetOfVar) =
        match goal with
        | Unify (lhs, rhs, _, _) -> unifyRhsVars rhs (TagSet.add lhs vars)
        | Call (_, args) -> List.fold (flip TagSet.add) vars args
        | FSharpCall (_, ret, args) -> List.fold (flip TagSet.add) vars (consOption ret args)
        | Conjunction (goals)
        | Disjunction (goals) -> List.fold (flip goalVars) vars goals
        | Switch (var, _, cases) ->
            let vars' = TagSet.add var vars
            List.fold (fun vars'' case -> goalVars case.CaseGoal vars'') vars' cases
        | IfThenElse (condGoal, thenGoal, elseGoal) -> List.fold (flip goalVars) vars [ condGoal; thenGoal; elseGoal ]
        | Not (negGoal) -> goalVars negGoal vars
        | Scope (_, subGoal) -> goalVars subGoal vars

    and goalVars (goal: Goal) vars = goalExprVars goal.Goal vars

    and unifyRhsVars rhs (vars: SetOfVar) =
        match rhs with
        | Var (var, _) -> TagSet.add var vars
        | Constructor (_, args, _, _, _) -> List.fold (flip TagSet.add) vars args
        | Lambda (nonLocals, args, _, _, goal) ->
            TagSet.union vars (TagSet.union (TagSet.ofList nonLocals) (TagSet.ofList args))
            |> goalVars goal
