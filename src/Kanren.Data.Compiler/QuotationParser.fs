namespace Kanren.Data.Compiler

open Kanren.Data
open FSharp.Reflection
open FSharp.Quotations
open FSharp.Collections

type ParserInfo = { varset: VarSet; errors: Error list; sourceInfo: SourceInfo }
    with
        member x.newVar(varType) =
            let (varset', var) = x.varset.newVar(varType)
            ({ x with varset = varset' }, var)

        member x.newError(error) =
            { x with errors = error :: x.errors }

        static member init varset sourceInfo = { varset = varset; errors = []; sourceInfo = sourceInfo }

module QuotationParser =

    type ParserState<'s, 'a> = ParserState of ('s -> ('a * 's))
 
    type StateFunc<'State, 'T> = 'State -> 'T * 'State

    type ParserStateFunc<'T> = StateFunc<ParserInfo, 'T>

    let inline run (stateFunc : StateFunc<'State, 'T>) initialState =
        stateFunc initialState
   
    type StateBuilder() =
       // 'T -> M<'T>
       member inline __.Return value
           : StateFunc<'State, 'T> =
           fun state ->
           value, state

       // M<'T> -> M<'T>
       member inline __.ReturnFrom func
           : StateFunc<'State, 'T> =
           func

       // unit -> M<'T>
       member inline this.Zero ()
           : StateFunc<'State, unit> =
           this.Return ()

       // M<'T> * ('T -> M<'U>) -> M<'U>
       member inline __.Bind (computation : StateFunc<_, 'T>, binder : 'T -> StateFunc<_,_>)
           : StateFunc<'State, 'U> =
           fun state ->
               let result, state = computation state
               (binder result) state

       // (unit -> M<'T>) -> M<'T>
       member inline this.Delay (generator : unit -> StateFunc<_,_>)
           : StateFunc<'State, 'T> =
           this.Bind (this.Return (), generator)

       // M<'T> -> M<'T> -> M<'T>
       // or
       // M<unit> -> M<'T> -> M<'T>
       member inline this.Combine (r1 : StateFunc<_,_>, r2 : StateFunc<_,_>)
           : StateFunc<'State, 'T> =
           this.Bind (r1, fun () -> r2)

       // M<'T> * (exn -> M<'T>) -> M<'T>
       member inline __.TryWith (computation : StateFunc<_,_>, catchHandler : exn -> StateFunc<_,_>)
           : StateFunc<'State, 'T> =
           fun state ->
               try computation state
               with ex ->
                   catchHandler ex state

       // M<'T> * (unit -> unit) -> M<'T>
       member inline __.TryFinally (computation : StateFunc<_,_>, compensation)
           : StateFunc<'State, 'T> =
           fun state ->
               try computation state
               finally
                   compensation ()

       // 'T * ('T -> M<'U>) -> M<'U> when 'T :> IDisposable
       member this.Using (resource : ('T :> System.IDisposable), binder : 'T -> StateFunc<_,_>)
           : StateFunc<'State, 'U> =
           fun state ->
               try binder resource state
               finally
                   if not <| isNull (box resource) then
                       resource.Dispose ()

       // (unit -> bool) * M<'T> -> M<'T>
       member this.While (guard, body : StateFunc<'State, unit>)
           : StateFunc<'State, unit> =
           fun state ->
               let mutable state = state
               while guard () do
                   state <- snd <| body state
               (), state

       // seq<'T> * ('T -> M<'U>) -> M<'U>
       // or
       // seq<'T> * ('T -> M<'U>) -> seq<M<'U>>
       member inline this.For (sequence : seq<_>, body : 'T -> StateFunc<_,_>)
           : StateFunc<'State, unit> =
           this.Using (sequence.GetEnumerator (),
               (fun enum ->
                   this.While (
                       enum.MoveNext,
                       this.Delay (fun () ->
                           body enum.Current))))


    let parse = new StateBuilder()

    let getSourceInfo (e:Quotations.Expr) = 
            match e with
            | DerivedPatterns.SpecificCall(<@@ kanren.exists @@>) (_, _,
                                                                        [_;
                                                                        DerivedPatterns.String(file);
                                                                        DerivedPatterns.Int32(line)])
            | DerivedPatterns.SpecificCall(<@@ kanren.call @@>) (_, _,
                                                                          [_; _;
                                                                          DerivedPatterns.String(file);
                                                                          DerivedPatterns.Int32(line)]) ->
                Some { SourceInfo.File = file; StartLine = line; StartCol = 0; EndLine = line; EndCol = 0 }     
            | _ ->
                let (|Val|_|) e : 't option = 
                    match e with
                    | Quotations.Patterns.Value(:? 't as v,_) -> Some v
                    | _ -> None

                let matchAttr attr =
                    match attr with
                    | Patterns.NewTuple [Val ("DebugRange");
                                            Patterns.NewTuple [Val(file:string);
                                                Val(startLine:int); 
                                                Val(startCol:int);
                                                Val(endLine:int);
                                                Val(endCol:int)]]
                        -> Some { SourceInfo.File = file; StartLine = startLine; StartCol = startCol; EndLine = endLine; EndCol = endCol } 
                    | _ -> None

                e.CustomAttributes |> List.tryPick matchAttr

    let updateSourceInfo expr parserInfo = ((),
                                                match (getSourceInfo expr) with
                                                | Some sourceInfo -> 
                                                    { parserInfo with ParserInfo.sourceInfo = sourceInfo }
                                                | None ->
                                                    parserInfo
                                                )

    let currentSourceInfo (parserInfo: ParserInfo) = (parserInfo.sourceInfo, parserInfo)

    let newVar varType (parserInfo: ParserInfo) =
        let (parserInfo', var) = parserInfo.newVar(varType)
        (var, parserInfo')

    let newVars varTypes (parserInfo: ParserInfo) =
        let (vars, parserInfo') =  List.mapFold (fun (p: ParserInfo) (t: System.Type) -> swap (p.newVar(t))) parserInfo varTypes
        (vars, parserInfo')

    let newError error (parserInfo: ParserInfo) =
        let parserInfo' = parserInfo.newError(error)
        ((), parserInfo')

    let rec mapParse f list =
        parse {
            match list with
            | [] -> return []
            | x :: xs ->
                let! x' = f x
                let! xs' = mapParse f xs
                return x' :: xs'
            }    
                                               
    let rec foldParse f list =
        parse {
            match list with
            | [] -> return ()
            | x :: xs ->
                let! _ = f x
                return! foldParse f xs
        }

    let rec foldParse2 f state list =
        parse {
            match list with
            | [] -> return state
            | x :: xs ->
                let! state' = f x state
                return! foldParse2 f state' xs
        }

    let (|True'|_|) expr =
        match expr with
        | Patterns.Value (o, t) when t = typeof<bool> && (o :?> bool) = true ->
            Some expr
        | _ ->
            None
    
    let (|False'|_|) expr =
        match expr with
        | Patterns.Value (o, t) when t = typeof<bool> && (o :?> bool) = false ->
            Some expr
        | _ ->
            None

    let rec getVars (varset: VarSet) expr =
        match expr with
        | ExprShape.ShapeVar v -> varset.addQuotationVar(v)
        | ExprShape.ShapeLambda (v, subExpr) -> getVars (varset.addQuotationVar v) subExpr
        | ExprShape.ShapeCombination (combo, exprs) -> List.fold getVars varset exprs

    let initGoal (sourceInfo:SourceInfo) (goal:GoalExpr) =
            { goal = goal; info = GoalInfo.init(sourceInfo) }
 
    let listToGoal goals =
        match goals with
        | [goal] -> goal.goal
        | _ -> Conj(goals)


    let rec translateUnifyRhs rhs =
        parse {
            let! sourceInfo = currentSourceInfo
            match rhs with
            | ExprShape.ShapeVar v ->
                return ([], Some (UnifyRhs.Var v))
            | Patterns.Value(value, constType) ->
                return ([], Some (UnifyRhs.Constructor([], Constant(value, constType))))
            | Patterns.NewTuple(args) ->
                let! (argVars, extraGoals) = translateCallArgs false args
                return (extraGoals, Some (UnifyRhs.Constructor(argVars, Tuple)))
            | Patterns.NewRecord(recordType, args) ->
                let! (argVars, extraGoals) = translateCallArgs false args
                return (extraGoals, Some (UnifyRhs.Constructor(argVars, Record(recordType))))
            | Patterns.NewUnionCase(caseInfo, args) ->
                let! (argVars, extraGoals) = translateCallArgs false args
                return (extraGoals, Some (UnifyRhs.Constructor(argVars, UnionCase(caseInfo))))
            | Patterns.Call(None, callee, args) ->
                let! (argVars, extraGoals) = translateCallArgs false args
                let! returnVar = newVar callee.ReturnType
                let goal = FSharpCall(callee, returnVar, argVars)
                return List.append extraGoals [initGoal sourceInfo goal], Some (UnifyRhs.Var returnVar)
            | _ ->
                do! newError(Error.unsupportedExpressionError sourceInfo rhs)
                return ([], None)
        }
    and   
        translateCallArg allowDuplicateArgs (seenArgs: Var Set) (extraGoals: Goal list) arg =
            parse {
                let! sourceInfo = currentSourceInfo
                match arg with
                | ExprShape.ShapeVar v when not (allowDuplicateArgs && seenArgs.Contains(v)) ->
                    return (v, seenArgs.Add(v), extraGoals)
                | _ ->
                    let! var = newVar arg.Type
                    let! (extraGoals', rhsResult) = translateUnifyRhs arg
                    match rhsResult with
                    | Some rhs ->
                        return (var, seenArgs, initGoal sourceInfo (Unify(var, rhs)) :: extraGoals')
                    | None ->
                        return (var, seenArgs, extraGoals')
            }
    and
        translateCallArgs' allowDuplicateArgs (argVars, seenArgs, extraGoals) args =
            parse {
                match args with
                | [] ->
                    return (argVars, seenArgs, extraGoals)
                | arg :: otherArgs ->
                    let! (argVar, seenArgs', extraGoals') = translateCallArg allowDuplicateArgs seenArgs extraGoals arg
                    return! translateCallArgs' allowDuplicateArgs (argVar :: argVars, seenArgs', extraGoals') otherArgs
            }
    and
        translateCallArgs allowDuplicateArgs args =
            parse {
                let! (argVars, _, extraGoals) = translateCallArgs' allowDuplicateArgs ([], Set.empty, []) args
                return (List.rev argVars, extraGoals)
            }
    let translateCall callee args =
            parse {
                let! sourceInfo = currentSourceInfo
                let! (argVars, extraGoals) = translateCallArgs false args
                let call = initGoal sourceInfo (Goal.Call(callee, argVars))
                return listToGoal (List.rev (call :: extraGoals))
            }

    let rec translateUnify lhs rhs unifyType =
            parse {
                let! sourceInfo = currentSourceInfo
                let! (extraGoals1, rhsResult1) = translateUnifyRhs lhs
                let! (extraGoals2, rhsResult2) = translateUnifyRhs rhs
                match (rhsResult1, rhsResult2) with
                | (Some rhs1, Some rhs2) ->
                    match rhs1 with
                    | UnifyRhs.Var v ->
                        return listToGoal (List.concat [extraGoals1; extraGoals2;
                                                    [initGoal sourceInfo (Unify(v, rhs2)) ]])
                    | _ ->
                        match rhs2 with
                        | UnifyRhs.Var v ->
                            return listToGoal (List.concat [extraGoals1; extraGoals2;
                                                [initGoal sourceInfo (Unify(v, rhs1))]])
                        | _ ->
                            let! unifyVar = newVar unifyType
                            return listToGoal (List.concat [extraGoals1; extraGoals2;
                                        [initGoal sourceInfo (Unify(unifyVar, rhs1));
                                        initGoal sourceInfo (Unify(unifyVar, rhs2)) ]])
                | _ ->
                    // error.
                    return Conj(List.append extraGoals1 extraGoals2)
            }

    let unsupportedExpression (expr: Expr) =
            parse {
                let! sourceInfo = currentSourceInfo
                do! newError(Error.unsupportedExpressionError sourceInfo expr)
                return Disj([])
            }

    // Some dumpster diving to convert if-then-elses corresponding to source-level pattern matches
    // back into a disjunction. This can only be done where the disjuncts are mutually exclusive.
    let rec (|UnionMatch'|_|) seenCases exprToTest expr : Option<(Constructor * Expr) list * bool> =
        match expr with
            | Patterns.IfThenElse (Patterns.UnionCaseTest (caseExprToTest, case), thenExpr, elseExpr) when exprToTest = caseExprToTest ->
                match elseExpr with
                | UnionMatch' (case :: seenCases) exprToTest (cases, canFail) ->
                    Some (((UnionCase(case), thenExpr) :: cases), canFail)
                | False' _ ->
                    let allCases = FSharp.Reflection.FSharpType.GetUnionCases(case.DeclaringType)
                    let missingCases = Array.filter (fun c -> not (List.contains c seenCases)) allCases
                    let canFail = missingCases.Length > 1
                    Some ([(UnionCase(case), thenExpr)], canFail)
                | _ ->
                    let allCases = FSharp.Reflection.FSharpType.GetUnionCases(case.DeclaringType)
                    let missingCases = Array.filter (fun c -> not (List.contains c (case :: seenCases))) allCases
                    if (Array.length missingCases = 1) then
                        Some ([(UnionCase(case), thenExpr); (UnionCase(missingCases.[0]), elseExpr)], false)
                    else
                        None
            | _ ->
                None

    let (|UnionMatch|_|) expr : Option<Expr * (Constructor * Expr) list * bool> =
        match expr with
            | Patterns.IfThenElse (Patterns.UnionCaseTest (exprToTest, _), _, _) ->
                match expr with
                | UnionMatch' [] exprToTest (cases, canFail) ->
                    Some (exprToTest, cases, canFail)
                | _ ->
                    None
            | _ ->
                None

    // More dumpster diving to recognise chains of tuple, record or union case deconstruction.
    let rec (|Deconstruct|_|) expr : Option<((Var * Expr) list * Expr)> =
        match expr with
            | Patterns.Let(var, getExpr, subExpr) ->
                match getExpr with
                | Patterns.TupleGet(_, _) | Patterns.PropertyGet(_, _, _) ->
                    match subExpr with
                    | Deconstruct (getExprs, bottomSubExpr) ->
                        Some ((var, getExpr) :: getExprs, bottomSubExpr)
                    | _ ->
                        Some ([(var, getExpr)], subExpr)
                | _ ->
                    None
            | _ ->
                None

    type DeconstructVar = Expr * Constructor * (Var Option) array * System.Type array
    type DeconstructVars = List<DeconstructVar>

    let rec expandPropertyGet expr deconstructVars =
        match expr with
        | Patterns.TupleGet(tupleExpr, tupleIndex) ->
            let deconstructVars' = match tupleExpr with
                                    | ExprShape.ShapeVar _ ->
                                        deconstructVars
                                    | _ ->
                                        let (_, deconstructVars'') = expandPropertyGet tupleExpr deconstructVars
                                        deconstructVars''
            let argTypes = FSharpType.GetTupleElements tupleExpr.Type

            let argVars = seq { 0 .. (Array.length(argTypes) - 1) } |> Seq.map (fun i -> None) |> Array.ofSeq
            let result = (expr, Tuple, argVars, argTypes)
            (result, result :: deconstructVars')
        | Patterns.PropertyGet(Some termExpr, propertyInfo, []) ->
            let deconstructVars' = match termExpr with
                                    | ExprShape.ShapeVar _ ->
                                        deconstructVars
                                    | _ ->  
                                        let (_, deconstructVars'') = expandPropertyGet termExpr deconstructVars
                                        deconstructVars''

            let (ctor, argTypes) =
                if (FSharpType.IsUnion termExpr.Type) then
                    let cases = FSharpType.GetUnionCases termExpr.Type
                    let case = Seq.ofArray cases
                            |> Seq.filter (
                                    fun c ->
                                        c.GetFields()
                                            |> Seq.ofArray
                                            |> Seq.exists (fun f -> f.Name = propertyInfo.Name)
                                )
                            |> Seq.exactlyOne
                            

                    let argTypes = case.GetFields() |> Array.map (fun f -> f.PropertyType)
                    (UnionCase(case), argTypes)
                else if (FSharpType.IsRecord termExpr.Type) then
                    let argTypes = FSharpType.GetRecordFields(termExpr.Type) |> Array.map (fun f -> f.PropertyType)
                    (Record(termExpr.Type), argTypes)
                else
                    raise (System.Exception($"type not supported in deconstruct {termExpr.Type.Name}"))
            let argVars = seq { 0 .. (Array.length(argTypes) - 1) } |> Seq.map (fun i -> None)  |> Array.ofSeq
            let result = (expr, ctor, argVars, argTypes)
            (result, result :: deconstructVars')
         | _ ->
             raise (System.Exception($"expression not supported in deconstruct {expr}"))

    let rec collectDeconstructPropertyVars var expr index deconstructVars =
        match (List.tryFind (fun (e, _, _, _) -> e = expr) deconstructVars) with
        | Some (_, _, unifyArgs: Var Option [], _) ->
            match unifyArgs.[index] with
            | Some (unifyArgVar) ->
                raise (System.Exception("expression deconstructed twice"))
            | None ->
                Array.set unifyArgs index (Some var)
                deconstructVars
        | None ->
            let ((_, _, argVars, _), deconstructVars') as newVar = expandPropertyGet expr deconstructVars
            Array.set argVars index (Some var)
            deconstructVars'
 
    let collectDeconstructVars deconstructVars (var, expr) =
         match expr with
         | Patterns.TupleGet(tupleExpr, index) ->
             collectDeconstructPropertyVars var expr index deconstructVars
         | Patterns.PropertyGet(Some termExpr, propertyInfo, []) ->
             if (FSharpType.IsRecord propertyInfo.DeclaringType) then
                 let fields = FSharpType.GetRecordFields propertyInfo.DeclaringType
                 let index = fields |> Array.findIndex (fun p -> p.Name = propertyInfo.Name)
                 if (index <> -1) then
                     collectDeconstructPropertyVars var expr index deconstructVars
                 else
                     raise (System.Exception($"property {propertyInfo.Name} not found"))
                             
             //else if (FSharpType.IsUnion propertyInfo.DeclaringType) then
             else
                 raise (System.Exception($"union type not supported"))
         | _ ->
             deconstructVars

    let rec translateSubExpr expr =
            parse {
                do! updateSourceInfo expr
                let! sourceInfo = currentSourceInfo
                match expr with
                | DerivedPatterns.SpecificCall (<@@ kanren.exists @@>)
                                                (_, _, [ExprShape.ShapeLambda (v, expr); _; _]) ->
                    return! translateSubExpr expr
                | DerivedPatterns.SpecificCall (<@@ kanren.call @@>)
                                                (_, _, [Patterns.PropertyGet(_, callee, []);
                                                              Patterns.NewTuple(args); _; _]) ->
                    return! translateCall callee args
                | DerivedPatterns.SpecificCall (<@@ (=) @@>) (_, [unifyType], [lhs; rhs] ) ->
                    return! translateUnify lhs rhs unifyType
                | Patterns.Call(None, callee, args) ->
                    return! translateUnify (Expr.Value true) expr typeof<bool>
                | UnionMatch (ExprShape.ShapeVar v, cases, canFail) ->
                    let! caseGoals = translateMatchExpr v cases
                    return Disj(caseGoals)
                | DerivedPatterns.AndAlso (condExpr, thenExpr) ->
                    let! condGoal = translateSubExprGoal condExpr
                    let! thenGoal = translateSubExprGoal thenExpr
                    return Simplify.flattenConjunction [condGoal; thenGoal]
                | DerivedPatterns.OrElse (condExpr, elseExpr) ->
                    let! condGoal = translateSubExprGoal condExpr
                    let! elseGoal = translateSubExprGoal elseExpr
                    return Simplify.flattenDisjunction [condGoal; elseGoal]
                | Deconstruct (deconstructExprs, subExpr) ->
                    let! deconstructGoals = translateDeconstructExprs deconstructExprs
                    let! subGoal = translateSubExprGoal subExpr
                    return Conj(List.append deconstructGoals [subGoal])
                | Patterns.Let (v, binding, expr) ->
                    // Introduces a fresh variable and unifies it immediately.
                    let! unifyGoalExpr = translateUnify (Expr.Var v) binding v.Type
                    let! exprGoal = translateSubExprGoal expr
                    return Simplify.flattenConjunction [initGoal sourceInfo unifyGoalExpr; exprGoal]
                | True' _ ->
                    return Conj([])
                | False' _ ->
                    return Disj([])
                | ExprShape.ShapeVar v ->
                    if (v.Type = typeof<bool>) then
                        return Unify(v, Constructor([], Constant(true, typeof<bool>)))
                    else
                        return! unsupportedExpression expr
                | ExprShape.ShapeLambda (v, subExpr) ->
                    return! unsupportedExpression expr
                | ExprShape.ShapeCombination (combo, exprs) ->
                    return! unsupportedExpression expr
            }
    and
        translateSubExprGoal expr =
                parse {
                    let! sourceInfo = currentSourceInfo
                    let! goal = translateSubExpr expr
                    return initGoal sourceInfo goal
                }
    and
        translateMatchCase var (case, expr) goals =
            parse {
                let! sourceInfo = currentSourceInfo
                let fieldTypes =
                    match case with
                    | UnionCase(unionCase) ->
                        unionCase.GetFields() |> Array.map (fun f -> f.PropertyType) 
                    | _ ->
                        [||]
                        
                let! fieldVars = newVars (List.ofArray fieldTypes)
                let unifyGoal = Unify(var, Constructor(fieldVars, case))
                let! goal = translateSubExprGoal expr
                let disjunct = initGoal sourceInfo (Conj([initGoal sourceInfo unifyGoal; goal]))

                return disjunct :: goals
            }
    and
        translateMatchExpr var cases =
            parse {
                let! goals = foldParse2 (translateMatchCase var) [] cases
                return List.rev goals
            }
    and
        translateDeconstructExprs (deconstructExprs: (Var * Expr) list) =
            parse {
                let deconstructVars = List.fold collectDeconstructVars [] deconstructExprs |> List.rev
                return! translateDeconstructVars deconstructVars
            }
    and
        translateDeconstructVars (deconstructVars: DeconstructVars) =
            parse {
                let rec assignUnifyArgs (unifyArgTypes: System.Type array) (unifyArgs: Var option array) i =
                    parse {
                        if (i >= unifyArgTypes.Length) then
                            return []
                        else
                            let! unifyArgsVars = assignUnifyArgs unifyArgTypes unifyArgs (i + 1)
                            match unifyArgs.[i] with
                            | Some v ->
                                return v :: unifyArgsVars
                            | None ->
                                let! v = newVar unifyArgTypes.[i]
                                return v :: unifyArgsVars
                    }

                let assignVar ((expr: Expr, ctor, unifyArgs, unifyArgTypes) as var)  =
                                    parse {
                                        let! assignedVar = match expr with
                                                            | ExprShape.ShapeVar v -> parse { return v }
                                                            | _ -> newVar expr.Type
                                        let! unifyArgs' = assignUnifyArgs unifyArgTypes unifyArgs 0
                                        return (assignedVar, expr, ctor, unifyArgs')
                                    }
                let! assignedDeconstructVars = mapParse assignVar deconstructVars

                let generateDeconstructGoal sourceInfo (var, expr, ctor, unifyArgs) =
                                initGoal sourceInfo (Unify(var, Constructor(unifyArgs, ctor)))
                let! sourceInfo = currentSourceInfo
                return List.map (generateDeconstructGoal sourceInfo) assignedDeconstructVars
            }

    let rec translateArgs expr args =
        parse {
            let! parserInfo' = updateSourceInfo expr
            match expr with
                | Patterns.Let (arg, Patterns.TupleGet (_, _), subExpr) ->
                    return! translateArgs subExpr (arg :: args)
                | _ ->
                    let! goal = translateSubExprGoal expr
                    return (List.rev args, goal)
        }

    let translateExpr expr =
        parse {
            let! parserInfo' = updateSourceInfo expr
            match expr with
                | Patterns.Lambda (_, subExpr) ->
                    return! translateArgs subExpr []
                | _ ->
                    let! sourceInfo = currentSourceInfo
                    let! goalExpr = unsupportedExpression expr
                    return ([], initGoal sourceInfo goalExpr)
        }
