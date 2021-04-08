namespace Kanren.Data.Compiler

open Kanren.Data

open FSharp.Quotations

type ParserInfo = { varset: VarSet; errors: Error list }
    with
        member x.newVar(varType) =
            let (varset', var) = x.varset.newVar(varType)
            ({ x with varset = varset' }, var)

        member x.newError(error) =
            { x with errors = error :: x.errors }

module QuotationParser =

    let getSourceInfo (s:SourceInfo Option) (e:Quotations.Expr) = 
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

        e.CustomAttributes |> List.tryPick matchAttr |> function | Some x -> Some x | None -> s

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
        | ExprShape.ShapeVar v -> varset.addVar(v)
        | ExprShape.ShapeLambda (v, subExpr) -> getVars (varset.addVar v) subExpr
        | ExprShape.ShapeCombination (combo, exprs) -> List.fold getVars varset exprs

    let initGoal (sourceInfo:SourceInfo Option) (expr:Expr) (goal:GoalExpr) = { goal = goal; info = GoalInfo.init(getSourceInfo sourceInfo expr) }
    
    let rec translateUnifyRhs sourceInfo rhs parserInfo =
        match rhs with
        | ExprShape.ShapeVar v ->
            (parserInfo, [], UnifyRhs.Var v)
        | Patterns.Value (value, constType) ->
            (parserInfo, [], UnifyRhs.Constant(value, constType))
        | Patterns.Call (None, callee, args) ->
            let (argVars, (parserInfo' : ParserInfo, _, extraGoals)) = translateCallArgs sourceInfo false args parserInfo
            let (parserInfo'', returnVar) = parserInfo'.newVar callee.ReturnType
            (parserInfo'', List.append extraGoals [initGoal sourceInfo rhs (FSharpCall(callee, returnVar, argVars))], UnifyRhs.Var returnVar)
        | _ ->
            raise(System.Exception($"Unsupported unify rhs: {rhs}"))
    and   
        translateCallArg sourceInfo allowDuplicateArgs (parserInfo: ParserInfo, seenArgs: Var Set, extraGoals: Goal list) arg =
            match arg with
            | ExprShape.ShapeVar v when not (allowDuplicateArgs && seenArgs.Contains(v)) ->
                (v, (parserInfo, seenArgs.Add(v), extraGoals))
            | _ ->
                let (parserInfo', var) = parserInfo.newVar(arg.Type)
                let (parserInfo'', extraGoals', rhs) = translateUnifyRhs sourceInfo arg parserInfo'
                (var, (parserInfo'', seenArgs, initGoal sourceInfo arg (Unify(var, rhs)) :: extraGoals'))
    and
        translateCallArgs sourceInfo allowDuplicateArgs args (parserInfo: ParserInfo) =
            List.mapFold (translateCallArg sourceInfo allowDuplicateArgs) (parserInfo, Set.empty, []) args

    let translateCall sourceInfo callee args (parserInfo: ParserInfo) =
            let (argVars, (parserInfo', _, extraGoals)) = translateCallArgs sourceInfo false args parserInfo
            let call = initGoal sourceInfo args.Head (Goal.Call(callee, argVars))
            (parserInfo', Conj(List.rev (call :: extraGoals)))

    let rec translateUnify sourceInfo lhs rhs unifyType (parserInfo: ParserInfo) =
            match lhs with
            | ExprShape.ShapeVar v ->
                let (parserInfo', extraGoals, rhs) = translateUnifyRhs sourceInfo rhs parserInfo
                (match extraGoals with
                    | [] ->
                        (parserInfo', Unify(v, rhs))
                    | _ :: _ ->
                        let unifyGoal = initGoal sourceInfo lhs (Unify(v, rhs))
                        (parserInfo', Conj(List.append extraGoals [unifyGoal]))
                )
            | _ ->
                match rhs with
                | ExprShape.ShapeVar v ->
                    translateUnify sourceInfo rhs lhs unifyType parserInfo
                | _ ->
                    let (parserInfo2, lvar) = parserInfo.newVar(unifyType)
                    let (parserInfo3, rvar) = parserInfo2.newVar(unifyType)
                    let (parserInfo4, extraGoals1, rhs1) = translateUnifyRhs sourceInfo lhs parserInfo3
                    let (parserInfo5, extraGoals2, rhs2) = translateUnifyRhs sourceInfo rhs parserInfo4
                    ( parserInfo5, Conj(List.concat [extraGoals1; extraGoals2;
                                        [initGoal sourceInfo lhs (Unify(lvar, rhs1));
                                            initGoal sourceInfo rhs (Unify(rvar, rhs2));
                                            initGoal sourceInfo lhs (Unify(lvar, UnifyRhs.Var rvar)) ]]))

    let unsupportedExpression sourceInfo (expr: Expr) (parserInfo: ParserInfo) : (ParserInfo * GoalExpr) =
            (parserInfo.newError({ Error.Location = sourceInfo; Text = "Unsupported expression"; Context = ErrorContext.Expr expr }),
                Disj([]))

    let rec translateSubExpr existingSourceInfo expr (parserInfo : ParserInfo) =
            let exprSourceInfo = getSourceInfo existingSourceInfo expr
            match expr with
            | DerivedPatterns.SpecificCall (<@@ call @@>) (_, _, [Patterns.PropertyGet (None, prop, _); Patterns.NewTuple (args)] ) ->
                translateCall exprSourceInfo prop args parserInfo
            | DerivedPatterns.SpecificCall (<@@ exists @@>) (_, _, [ExprShape.ShapeLambda (v, expr)] ) ->
                translateSubExpr exprSourceInfo expr parserInfo
            | DerivedPatterns.SpecificCall (<@@ (=) @@>) (_, [unifyType], [lhs; rhs] ) ->
                translateUnify exprSourceInfo lhs rhs unifyType parserInfo
            | Patterns.Call(None, callee, args) ->
                let (parserInfo', var) = parserInfo.newVar(typeof<bool>)
                translateUnify exprSourceInfo (Expr.Value true) expr typeof<bool> parserInfo' 
            | DerivedPatterns.AndAlso (condExpr, thenExpr) ->
                let (parserInfo', condGoal) = translateSubExprGoal exprSourceInfo condExpr parserInfo
                let (parserInfo'', thenGoal) = translateSubExprGoal exprSourceInfo thenExpr parserInfo'
                (parserInfo'', Conj([condGoal; thenGoal]))
            | DerivedPatterns.OrElse (condExpr, elseExpr) ->
                let (parserInfo', condGoal) = translateSubExprGoal exprSourceInfo condExpr parserInfo
                let (parserInfo'', elseGoal) = translateSubExprGoal exprSourceInfo elseExpr parserInfo'
                (parserInfo'', Disj([condGoal; elseGoal]))
            | True' _ ->
                (parserInfo, Conj([]))
            | False' _ ->
                (parserInfo, Disj([]))
            | ExprShape.ShapeVar v ->
                if (v.Type = typeof<bool>) then
                    (parserInfo, Unify(v, Constant(true, typeof<bool>)))
                else
                    unsupportedExpression exprSourceInfo expr parserInfo
            | ExprShape.ShapeLambda (v, subExpr) ->
                unsupportedExpression exprSourceInfo expr parserInfo
            | ExprShape.ShapeCombination (combo, exprs) ->
                unsupportedExpression exprSourceInfo expr parserInfo
    and
        translateSubExprGoal sourceInfo expr parserInfo =
                let (parserInfo', goal) = translateSubExpr sourceInfo expr parserInfo
                (parserInfo', initGoal sourceInfo expr goal)

    let rec translateArgs sourceInfo expr parserInfo =
        let exprSourceInfo = getSourceInfo sourceInfo expr
        match expr with
            | Patterns.Let (_, Patterns.TupleGet (_, _), subExpr) ->
                translateArgs exprSourceInfo subExpr parserInfo
            | _ ->
                translateSubExprGoal exprSourceInfo expr parserInfo

    let translateExpr sourceInfo expr (parserInfo : ParserInfo) =
        let exprSourceInfo = getSourceInfo sourceInfo expr
        match expr with
            | Patterns.Lambda (_, subExpr) -> translateArgs exprSourceInfo subExpr parserInfo
            | _ -> raise (System.Exception($"Expected lambda at top level of clause"))
