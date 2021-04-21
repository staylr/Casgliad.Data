namespace Kanren.Data.Compiler

open Kanren.Data
open System.Reflection

open FSharp.Quotations

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
    let inline run state x = let (ParserState(f)) = x in f state

    type ParserStateBuilder() =
        member this.Zero () = ParserState(fun s -> (), s)
        member this.Return x = ParserState(fun s -> x, s)
        member inline this.ReturnFrom (x: ParserState<'s, 'a>) = x
        member this.Bind (x, f) : ParserState<'s, 'b> =
            ParserState(fun state ->
                let (result: 'a), state = run state x
                run state (f result))
        member this.Combine (x1: ParserState<'s, 'a>, x2: ParserState<'s, 'b>) =
            ParserState(fun state ->
                let result, state = run state x1
                run state x2)

    let parse = new ParserStateBuilder()

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

    let updateSourceInfo expr = ParserState(fun parserInfo ->
                                                (),
                                                match (getSourceInfo expr) with
                                                | Some sourceInfo -> 
                                                    { parserInfo with ParserInfo.sourceInfo = sourceInfo }
                                                | None ->
                                                    parserInfo
                                                )

    let currentSourceInfo = ParserState(fun (parserInfo: ParserInfo) -> (parserInfo.sourceInfo, parserInfo))

    let newVar varType = ParserState(fun (parserInfo: ParserInfo) ->
                                            let (parserInfo', var) = parserInfo.newVar(varType)
                                            (var, parserInfo'))

    let newVars varTypes = ParserState(fun (parserInfo: ParserInfo) ->
                                            let (vars, parserInfo') =  List.mapFold (fun (p: ParserInfo) (t: System.Type) -> swap (p.newVar(t))) parserInfo varTypes
                                            (vars, parserInfo'))

    let newError error = ParserState(fun (parserInfo: ParserInfo) ->
                                               let parserInfo' = parserInfo.newError(error)
                                               ((), parserInfo'))

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
    // back into a list of cases.
    let rec (|UnionMatch'|_|) seenCases exprToTest expr : Option<(FSharp.Reflection.UnionCaseInfo * Expr) list * bool> =
        match expr with
            | Patterns.IfThenElse (Patterns.UnionCaseTest (caseExprToTest, case), thenExpr, elseExpr) when exprToTest = caseExprToTest ->
                match elseExpr with
                | UnionMatch' (case :: seenCases) exprToTest (cases, canFail) ->
                    Some (((case, thenExpr) :: cases), canFail)
                | False' _ ->
                    let allCases = FSharp.Reflection.FSharpType.GetUnionCases(case.DeclaringType)
                    let missingCases = Array.filter (fun c -> not (List.contains c seenCases)) allCases
                    let canFail = missingCases.Length > 1
                    Some ([(case, thenExpr)], canFail)
                | _ ->
                    let allCases = FSharp.Reflection.FSharpType.GetUnionCases(case.DeclaringType)
                    let missingCases = Array.filter (fun c -> not (List.contains c (case :: seenCases))) allCases
                    if (Array.length missingCases = 1) then
                        Some ([(case, thenExpr); (missingCases.[0], elseExpr)], false)
                    else
                        None
            | _ ->
                None

    let (|UnionMatch|_|) expr : Option<Expr * (FSharp.Reflection.UnionCaseInfo * Expr) list * bool> =
        match expr with
            | Patterns.IfThenElse (Patterns.UnionCaseTest (exprToTest, _), _, _) ->
                do System.Console.WriteLine($"found case {exprToTest}")
                match expr with
                | UnionMatch' [] exprToTest (cases, canFail) ->
                    Some (exprToTest, cases, canFail)
                | _ ->
                    None
            | _ ->
                None

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
                    return Conj([condGoal; thenGoal])
                | DerivedPatterns.OrElse (condExpr, elseExpr) ->
                    let! condGoal = translateSubExprGoal condExpr
                    let! elseGoal = translateSubExprGoal elseExpr
                    return Disj([condGoal; elseGoal])
                | Patterns.Let (v, binding, expr) ->
                    // Introduces a fresh variable and unifies it immediately.
                    let! unifyGoalExpr = translateUnify (Expr.Var v) binding v.Type
                    let! exprGoal = translateSubExprGoal expr
                    return Conj([initGoal sourceInfo unifyGoalExpr; exprGoal])
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
        translateMatchExpr var cases =
            parse {
                match cases with
                | [] ->
                    return []
                | (case, expr) :: cases' ->
                    let! sourceInfo = currentSourceInfo
                    let fieldTypes = case.GetFields() |> Array.map (fun f -> f.PropertyType) 
                    let! fieldVars = newVars (List.ofArray fieldTypes)  
                    let unifyGoal = Unify(var, Constructor(fieldVars, UnionCase(case)))
                    let! goal = translateSubExprGoal expr
                    let disjunct = initGoal sourceInfo (Conj([initGoal sourceInfo unifyGoal; goal]))

                    let! otherGoals = translateMatchExpr var cases'
                    return disjunct :: otherGoals
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
