namespace Kanren.Data.Compiler

open Kanren.Data
open System.CodeDom.Compiler

module GoalWriter =

    [<System.Flags>]
    type GoalToStringFlags =
    | None = 0
    | PrintInfo = 1

    type GoalToStringInfo = { Writer: System.CodeDom.Compiler.IndentedTextWriter; VarSet: VarSet; Flags: GoalToStringFlags }

    type GoalToStringFunc = GoalToStringInfo -> unit
 
    type GoalToStringBuilder () =
        member inline __.Yield (txt: string) = fun (b: GoalToStringInfo) -> b.Writer.Write txt |> ignore
        member inline __.Yield (c: char) = fun (b: GoalToStringInfo) -> b.Writer.Write c |> ignore
        member inline __.Yield (v: VarId) =
            fun (b: GoalToStringInfo) ->
                let var = b.VarSet.[v]
                b.Writer.Write var.Name |> ignore
        member inline __.Yield (vs: VarId list) =
            fun (b: GoalToStringInfo) ->
                match vs with
                | v :: vs' ->
                    b |> __.Yield("(")
                    b |> __.Yield(v)
                    for v' in vs' do
                       b |> __.Yield(", ")
                       b |> __.Yield(v')
                    b |> __.Yield(')')
                | _ ->
                    b |> __.Yield(')')
        member inline __.Yield (strings: #seq<string>) =
            fun (b: GoalToStringInfo) -> for s in strings do s |> b.Writer.WriteLine |> ignore
        member inline __.YieldFrom (f: GoalToStringFunc) = f
        member __.Combine (f, g) = fun (b: GoalToStringInfo) -> f b; g b
        member __.Delay f = fun (b: GoalToStringInfo) -> (f()) b
        member __.Zero () = ignore
         
        member __.For (xs: 'a seq, f: 'a -> GoalToStringFunc) =
            fun (b: GoalToStringInfo) ->
                let e = xs.GetEnumerator ()
                while e.MoveNext() do
                    (f e.Current) b
         
        member __.While (p: unit -> bool, f: GoalToStringFunc) =
            fun (b: GoalToStringInfo) -> while p () do f b
             
        member __.Run (f: GoalToStringFunc) = f
 
    let gts = new GoalToStringBuilder()

    let indent (f: GoalToStringFunc) (info: GoalToStringInfo) =
            do info.Writer.Indent <- info.Writer.Indent + 4
            do info.Writer.WriteLine()
            do f info
            do info.Writer.Indent <- info.Writer.Indent - 4
            do info.Writer.WriteLine()
            ()

    let rec listToString l f (sep: string) =
        gts {
            match l with
            | x::xs ->
                yield! f x
                match xs with
                | _ :: _ ->
                    yield sep
                | [] ->
                    yield! listToString xs f sep
            | [] ->
                ()
        }

[<AutoOpen>]
module Goal =

    open GoalWriter

    type SetOfVar = TagSet<varIdMeasure>

    let emptySetOfVar = TagSet.empty<varIdMeasure>

    type Instmap = Map<VarId, Kanren.Data.Inst>

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
                nonLocals = TagSet.empty<varIdMeasure>;
                instmapDelta = Map.empty;
                determinism = Determinism.Det;
                sourceInfo = sourceInfo;
            }

    type Constructor =
        | Constant of value: obj * constType: System.Type
        | Tuple
        | Record of System.Type
        | UnionCase of FSharp.Reflection.UnionCaseInfo
        member x.Dump() : GoalToStringFunc =
            gts {
                match x with
                | Constant (constVal, _) ->
                    yield constVal.ToString()
                | Tuple ->
                    yield "Tuple"
                | Record t ->
                    yield "Record "
                    yield t.Name
                | UnionCase (uci) ->
                    yield uci.Name
            }


    type VarVarUnifyType =
    | Assign
    | Test

    type VarCtorUnifyType =
    | Construct
    | Deconstruct

    type UnifyMode = Mode * Mode

    type UnifyMainContext =
    | ExplicitUnify
    | HeadUnify of ArgIndex: int
    | CallArgUnify of Name: string * ArgIndex: int
    | ImplicitUnify 

    type UnifySubContextFunctor =
    | FunctorConstructor of Constructor
    | FunctorCall of System.Reflection.MethodInfo

    type UnifySubContext = { Functor: UnifySubContextFunctor; ArgIndex: int } 

    type UnifyContext = { MainContext: UnifyMainContext; SubContext: UnifySubContext list }

    let initUnifyContext mainContext = { MainContext = mainContext; SubContext = [] }

    type GoalExpr =
        | Unify of lhs: VarId * rhs : UnifyRhs * mode: UnifyMode * context: UnifyContext
        | Call of func: System.Reflection.PropertyInfo * args: (VarId list)
        | FSharpCall of func: System.Reflection.MethodInfo * returnValue: VarId * args : (VarId list)
        | Conj of Goal list
        | Disj of Goal list
        | Switch of var: VarId * canFail: bool * cases: Case list
        | IfThenElse of condGoal: Goal * thenGoal: Goal * elseGoal: Goal
        | Not of Goal
        with
        member x.Dump() : GoalToStringFunc =
            gts {
                match x with
                | Unify (lhs, rhs, _, _) ->
                    yield lhs
                    yield " = "
                    yield! rhs.Dump()
                | Call (property, args) ->
                    yield property.Name
                    yield args
                | FSharpCall(method, returnValue, args) ->
                    yield returnValue
                    yield " = F#"
                    yield method.Name
                    yield args
                | Conj(goals) ->
                    yield! indent (listToString goals (fun goal -> goal.Dump()) ",\n")
                | Disj(goals) ->
                    yield "("
                    yield! indent (listToString goals (fun goal -> goal.Dump()) ";\n")
                | Switch(var, canFail, cases) ->
                    yield ""
                | IfThenElse(condGoal, thenGoal, elseGoal) ->
                    yield ""
                | Not(negGoal) ->
                    yield " not ("
                    yield! indent (negGoal.Dump())
                    yield ")"
            }
    and
        Goal = { goal : GoalExpr; info : GoalInfo }
        with
        member x.Dump() =
            gts { yield! x.goal.Dump() }
    and
        Case = { constructor: Constructor; otherConstructors: Constructor list; caseGoal: Goal }
    and
        UnifyRhs =
        | Var of var: VarId * unifyType: VarVarUnifyType
        | Constructor of constructor: Constructor
                        * args: VarId list
                        * unifyType: VarCtorUnifyType
                        * argModes: UnifyMode list
        | Lambda of nonLocals: VarId list
                        * args: VarId list
                        * modes: Mode list
                        * detism: Determinism
                        * goal: Goal
        with
        member x.Dump() : GoalToStringFunc =
            gts {
                match x with
                | Var(v, _) ->
                    yield v
                | Constructor(ctor, args, _, _) ->
                    yield! ctor.Dump()
                    match args with
                    | _ :: _ ->
                        yield args
                    | [] ->
                        yield ""
                | Lambda(_, _, _, _, _) ->
                    yield ("lambda")
            }

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

    let rec goalExprVars goal (vars : SetOfVar) =
        match goal with
            | Unify(lhs, rhs, _, _) ->
                unifyRhsVars rhs (TagSet.add lhs vars)
            | Call(_, args) ->
                List.fold (flip TagSet.add) vars args
            | FSharpCall(_, ret, args) ->
                 List.fold (flip TagSet.add) vars (ret :: args)
            | Conj(goals)
            | Disj(goals) ->
                List.fold (flip goalVars) vars goals
            | Switch(var, _, cases) ->
                let vars' = TagSet.add var vars
                List.fold (fun vars'' case -> goalVars case.caseGoal vars'') vars' cases
            | IfThenElse(condGoal, thenGoal, elseGoal) ->
                List.fold (flip goalVars) vars [condGoal; thenGoal; elseGoal]
            | Not(negGoal) ->
                goalVars negGoal vars
    and
        goalVars (goal : Goal) vars = goalExprVars goal.goal vars
    and
        unifyRhsVars rhs (vars : SetOfVar) =
            match rhs with
                | Var (var, _) -> TagSet.add var vars
                | Constructor (_, args, _, _) -> List.fold (flip TagSet.add) vars args
                | Lambda (nonLocals, args, _, _, goal) ->
                    TagSet.union vars (TagSet.union (TagSet.ofList nonLocals) (TagSet.ofList args))
                    |> goalVars goal
