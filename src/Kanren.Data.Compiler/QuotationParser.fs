namespace Kanren.Data.Compiler

open Kanren.Data
open System.Reflection

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
        | ExprShape.ShapeVar v -> varset.addQuotationVar(v)
        | ExprShape.ShapeLambda (v, subExpr) -> getVars (varset.addQuotationVar v) subExpr
        | ExprShape.ShapeCombination (combo, exprs) -> List.fold getVars varset exprs

    let initGoal (sourceInfo:SourceInfo Option) (expr:Expr) (goal:GoalExpr) =
            { goal = goal; info = GoalInfo.init(getSourceInfo sourceInfo expr) }
 
    let rec translateUnifyRhs sourceInfo rhs parserInfo =
        match rhs with
        | ExprShape.ShapeVar v ->
            (parserInfo, [], Some (UnifyRhs.Var v))
        | Patterns.Value (value, constType) ->
            (parserInfo, [], Some (UnifyRhs.Constant(value, constType)))
        | Patterns.Call (None, callee, args) ->
            let (argVars, (parserInfo' : ParserInfo, _, extraGoals)) = translateCallArgs sourceInfo false args parserInfo
            let (parserInfo'', returnVar) = parserInfo'.newVar callee.ReturnType
            let goal = FSharpCall(callee, returnVar, argVars)
            (parserInfo'', List.append extraGoals [initGoal sourceInfo rhs goal], Some (UnifyRhs.Var returnVar))
        | _ ->
            (parserInfo.newError(Error.unsupportedExpressionError sourceInfo rhs), [], None)
    and   
        translateCallArg sourceInfo allowDuplicateArgs (parserInfo: ParserInfo, seenArgs: Var Set, extraGoals: Goal list) arg =
            match arg with
            | ExprShape.ShapeVar v when not (allowDuplicateArgs && seenArgs.Contains(v)) ->
                (v, (parserInfo, seenArgs.Add(v), extraGoals))
            | _ ->
                let (parserInfo', var) = parserInfo.newVar(arg.Type)
                let (parserInfo'', extraGoals', rhsResult) = translateUnifyRhs sourceInfo arg parserInfo'
                match rhsResult with
                | Some rhs ->
                    (var, (parserInfo'', seenArgs, initGoal sourceInfo arg (Unify(var, rhs)) :: extraGoals'))
                | None ->
                    (var, (parserInfo'', seenArgs, extraGoals'))
    and
        translateCallArgs sourceInfo allowDuplicateArgs args (parserInfo: ParserInfo) =
            List.mapFold (translateCallArg sourceInfo allowDuplicateArgs) (parserInfo, Set.empty, []) args

    let translateCall sourceInfo callee args (parserInfo: ParserInfo) =
            let (argVars, (parserInfo', _, extraGoals)) = translateCallArgs sourceInfo false args parserInfo
            let call = initGoal sourceInfo args.Head (Goal.Call(callee, argVars))
            (parserInfo', Conj(List.rev (call :: extraGoals)))

    let rec translateUnify sourceInfo lhs rhs unifyType (parserInfo: ParserInfo) =
                let (parserInfo', extraGoals1, rhsResult1) = translateUnifyRhs sourceInfo lhs parserInfo
                let (parserInfo'', extraGoals2, rhsResult2) = translateUnifyRhs sourceInfo rhs parserInfo'
                match (rhsResult1, rhsResult2) with
                | (Some rhs1, Some rhs2) ->
                    match rhs1 with
                    | UnifyRhs.Var v ->
                        ( parserInfo'', Conj(List.concat [extraGoals1; extraGoals2;
                                                    [initGoal sourceInfo rhs (Unify(v, rhs2)) ]]))
                    | _ ->
                        match rhs2 with
                        | UnifyRhs.Var v ->
                            ( parserInfo'', Conj(List.concat [extraGoals1; extraGoals2;
                                                [initGoal sourceInfo lhs (Unify(v, rhs1))]]))
                        | _ ->
                            let (parserInfo''', unifyVar) = parserInfo''.newVar(unifyType)
                            ( parserInfo''', Conj(List.concat [extraGoals1; extraGoals2;
                                        [initGoal sourceInfo lhs (Unify(unifyVar, rhs1));
                                        initGoal sourceInfo rhs (Unify(unifyVar, rhs2)) ]]))
                | _ ->
                    (parserInfo'', Conj(List.append extraGoals1 extraGoals2))

    let unsupportedExpression sourceInfo (expr: Expr) (parserInfo: ParserInfo) : (ParserInfo * GoalExpr) =
            (parserInfo.newError(Error.unsupportedExpressionError sourceInfo expr), Disj([]))

    let rec translateSubExpr existingSourceInfo expr (parserInfo : ParserInfo) =
            let exprSourceInfo = getSourceInfo existingSourceInfo expr
            match expr with
            | DerivedPatterns.SpecificCall (<@@ exists @@>) (_, _, [ExprShape.ShapeLambda (v, expr)] ) ->
                translateSubExpr exprSourceInfo expr parserInfo
            | DerivedPatterns.SpecificCall (<@@ call @@>) (_, _, [Patterns.PropertyGet(_, callee, []); Patterns.NewTuple(args)]) ->
                translateCall exprSourceInfo callee args parserInfo
            | DerivedPatterns.SpecificCall (<@@ (=) @@>) (_, [unifyType], [lhs; rhs] ) ->
                translateUnify exprSourceInfo lhs rhs unifyType parserInfo
            | Patterns.Call(None, callee, args) ->
                translateUnify exprSourceInfo (Expr.Value true) expr typeof<bool> parserInfo
            | DerivedPatterns.AndAlso (condExpr, thenExpr) ->
                let (parserInfo', condGoal) = translateSubExprGoal exprSourceInfo condExpr parserInfo
                let (parserInfo'', thenGoal) = translateSubExprGoal exprSourceInfo thenExpr parserInfo'
                (parserInfo'', Conj([condGoal; thenGoal]))
            | DerivedPatterns.OrElse (condExpr, elseExpr) ->
                let (parserInfo', condGoal) = translateSubExprGoal exprSourceInfo condExpr parserInfo
                let (parserInfo'', elseGoal) = translateSubExprGoal exprSourceInfo elseExpr parserInfo'
                (parserInfo'', Disj([condGoal; elseGoal]))
            | Patterns.Let (v, binding, expr) ->
                // Introduces a fresh variable and unifies it immediately.
                let (parserInfo', unifyGoalExpr) = translateUnify exprSourceInfo (Expr.Var v) binding v.Type parserInfo
                let (parserInfo'', exprGoal) = translateSubExprGoal exprSourceInfo expr parserInfo'
                (parserInfo'', Conj([initGoal exprSourceInfo binding unifyGoalExpr; exprGoal]))
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

    let rec translateArgs sourceInfo expr parserInfo args =
        let exprSourceInfo = getSourceInfo sourceInfo expr
        match expr with
            | Patterns.Let (arg, Patterns.TupleGet (_, _), subExpr) ->
                translateArgs exprSourceInfo subExpr parserInfo (arg :: args)
            | _ ->
                let (parserInfo', goal) = translateSubExprGoal exprSourceInfo expr parserInfo
                (parserInfo', List.rev args, goal)

    let translateExpr sourceInfo expr (parserInfo : ParserInfo) =
        let exprSourceInfo = getSourceInfo sourceInfo expr
        match expr with
            | Patterns.Lambda (_, subExpr) ->
                translateArgs exprSourceInfo subExpr parserInfo []
            | _ ->
                let (parserInfo', goalExpr) = unsupportedExpression sourceInfo expr parserInfo
                (parserInfo', [], initGoal sourceInfo expr goalExpr)
