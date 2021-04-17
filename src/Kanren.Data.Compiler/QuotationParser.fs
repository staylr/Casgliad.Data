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

    let updateSourceInfo expr parserInfo =
        let maybeSourceInfo = getSourceInfo expr
        match maybeSourceInfo with
        | Some sourceInfo -> 
            { parserInfo with ParserInfo.sourceInfo = sourceInfo }
        | None ->
            parserInfo

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

    let rec translateUnifyRhs rhs parserInfo =
        match rhs with
        | ExprShape.ShapeVar v ->
            (parserInfo, [], Some (UnifyRhs.Var v))
        | Patterns.Value(value, constType) ->
            (parserInfo, [], Some (UnifyRhs.Constant(value, constType)))
        | Patterns.NewTuple(args) ->
            let (argVars, (parserInfo': ParserInfo, _, extraGoals)) = translateCallArgs false args parserInfo
            (parserInfo', extraGoals, Some (UnifyRhs.Constructor(argVars, Tuple)))
        | Patterns.NewRecord(recordType, args) ->
            let (argVars, (parserInfo': ParserInfo, _, extraGoals)) = translateCallArgs false args parserInfo
            (parserInfo', extraGoals, Some (UnifyRhs.Constructor(argVars, Record(recordType))))
        | Patterns.NewUnionCase(caseInfo, args) ->
            let (argVars, (parserInfo': ParserInfo, _, extraGoals)) = translateCallArgs false args parserInfo
            (parserInfo', extraGoals, Some (UnifyRhs.Constructor(argVars, UnionCase(caseInfo))))
        | Patterns.Call(None, callee, args) ->
            let (argVars, (parserInfo': ParserInfo, _, extraGoals)) = translateCallArgs false args parserInfo
            let (parserInfo'', returnVar) = parserInfo'.newVar callee.ReturnType
            let goal = FSharpCall(callee, returnVar, argVars)
            (parserInfo'', List.append extraGoals [initGoal parserInfo.sourceInfo goal], Some (UnifyRhs.Var returnVar))
        | _ ->
            (parserInfo.newError(Error.unsupportedExpressionError parserInfo.sourceInfo rhs), [], None)
    and   
        translateCallArg allowDuplicateArgs (parserInfo: ParserInfo, seenArgs: Var Set, extraGoals: Goal list) arg =
            match arg with
            | ExprShape.ShapeVar v when not (allowDuplicateArgs && seenArgs.Contains(v)) ->
                (v, (parserInfo, seenArgs.Add(v), extraGoals))
            | _ ->
                let (parserInfo', var) = parserInfo.newVar(arg.Type)
                let (parserInfo'', extraGoals', rhsResult) = translateUnifyRhs arg parserInfo'
                match rhsResult with
                | Some rhs ->
                    (var, (parserInfo'', seenArgs, initGoal parserInfo.sourceInfo (Unify(var, rhs)) :: extraGoals'))
                | None ->
                    (var, (parserInfo'', seenArgs, extraGoals'))
    and
        translateCallArgs allowDuplicateArgs args (parserInfo: ParserInfo) =
            List.mapFold (translateCallArg allowDuplicateArgs) (parserInfo, Set.empty, []) args

    let translateCall callee args (parserInfo: ParserInfo) =
            let (argVars, (parserInfo', _, extraGoals)) = translateCallArgs false args parserInfo
            let call = initGoal parserInfo.sourceInfo (Goal.Call(callee, argVars))
            (parserInfo', listToGoal (List.rev (call :: extraGoals)))

    let rec translateUnify lhs rhs unifyType (parserInfo: ParserInfo) =
                let (parserInfo', extraGoals1, rhsResult1) = translateUnifyRhs lhs parserInfo
                let (parserInfo'', extraGoals2, rhsResult2) = translateUnifyRhs rhs parserInfo'
                match (rhsResult1, rhsResult2) with
                | (Some rhs1, Some rhs2) ->
                    match rhs1 with
                    | UnifyRhs.Var v ->
                        ( parserInfo'', listToGoal (List.concat [extraGoals1; extraGoals2;
                                                    [initGoal parserInfo''.sourceInfo (Unify(v, rhs2)) ]]))
                    | _ ->
                        match rhs2 with
                        | UnifyRhs.Var v ->
                            ( parserInfo'', listToGoal (List.concat [extraGoals1; extraGoals2;
                                                [initGoal parserInfo''.sourceInfo (Unify(v, rhs1))]]))
                        | _ ->
                            let (parserInfo''', unifyVar) = parserInfo''.newVar(unifyType)
                            ( parserInfo''', listToGoal (List.concat [extraGoals1; extraGoals2;
                                        [initGoal parserInfo'''.sourceInfo (Unify(unifyVar, rhs1));
                                        initGoal parserInfo'''.sourceInfo (Unify(unifyVar, rhs2)) ]]))
                | _ ->
                    (parserInfo'', Conj(List.append extraGoals1 extraGoals2))

    let unsupportedExpression (expr: Expr) (parserInfo: ParserInfo) : (ParserInfo * GoalExpr) =
            (parserInfo.newError(Error.unsupportedExpressionError parserInfo.sourceInfo expr), Disj([]))

    let rec translateSubExpr expr (parserInfo : ParserInfo) =
            let parserInfo' = updateSourceInfo expr parserInfo
            match expr with
            | DerivedPatterns.SpecificCall (<@@ kanren.exists @@>)
                                            (_, _, [ExprShape.ShapeLambda (v, expr); _; _]) ->
                translateSubExpr expr parserInfo'
            | DerivedPatterns.SpecificCall (<@@ kanren.call @@>)
                                            (_, _, [Patterns.PropertyGet(_, callee, []);
                                                          Patterns.NewTuple(args); _; _]) ->
                translateCall callee args parserInfo'
            | DerivedPatterns.SpecificCall (<@@ (=) @@>) (_, [unifyType], [lhs; rhs] ) ->
                translateUnify lhs rhs unifyType parserInfo'
            | Patterns.Call(None, callee, args) ->
                translateUnify (Expr.Value true) expr typeof<bool> parserInfo'
            | DerivedPatterns.AndAlso (condExpr, thenExpr) ->
                let (parserInfo'', condGoal) = translateSubExprGoal condExpr parserInfo'
                let (parserInfo''', thenGoal) = translateSubExprGoal thenExpr parserInfo''
                (parserInfo''', Conj([condGoal; thenGoal]))
            | DerivedPatterns.OrElse (condExpr, elseExpr) ->
                let (parserInfo'', condGoal) = translateSubExprGoal condExpr parserInfo'
                let (parserInfo''', elseGoal) = translateSubExprGoal elseExpr parserInfo''
                (parserInfo''', Disj([condGoal; elseGoal]))
            | Patterns.Let (v, binding, expr) ->
                // Introduces a fresh variable and unifies it immediately.
                let (parserInfo'', unifyGoalExpr) = translateUnify (Expr.Var v) binding v.Type parserInfo'
                let (parserInfo''', exprGoal) = translateSubExprGoal expr parserInfo''
                (parserInfo''', Conj([initGoal parserInfo'.sourceInfo unifyGoalExpr; exprGoal]))
            | True' _ ->
                (parserInfo', Conj([]))
            | False' _ ->
                (parserInfo', Disj([]))
            | ExprShape.ShapeVar v ->
                if (v.Type = typeof<bool>) then
                    (parserInfo', Unify(v, Constant(true, typeof<bool>)))
                else
                    unsupportedExpression expr parserInfo'
            | ExprShape.ShapeLambda (v, subExpr) ->
                unsupportedExpression expr parserInfo'
            | ExprShape.ShapeCombination (combo, exprs) ->
                unsupportedExpression expr parserInfo'
    and
        translateSubExprGoal expr parserInfo =
                let (parserInfo', goal) = translateSubExpr expr parserInfo
                (parserInfo', initGoal parserInfo'.sourceInfo goal)

    let rec translateArgs expr parserInfo args =
        let parserInfo' = updateSourceInfo expr parserInfo
        match expr with
            | Patterns.Let (arg, Patterns.TupleGet (_, _), subExpr) ->
                translateArgs subExpr parserInfo (arg :: args)
            | _ ->
                let (parserInfo', goal) = translateSubExprGoal expr parserInfo
                (parserInfo', List.rev args, goal)

    let translateExpr expr (parserInfo : ParserInfo) =
        let parserInfo' = updateSourceInfo expr parserInfo
        match expr with
            | Patterns.Lambda (_, subExpr) ->
                translateArgs subExpr parserInfo' []
            | _ ->
                let (parserInfo'', goalExpr) = unsupportedExpression expr parserInfo
                (parserInfo'', [], initGoal parserInfo'.sourceInfo goalExpr)
