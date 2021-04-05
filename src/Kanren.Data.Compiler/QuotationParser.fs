namespace Kanren.Data.Compiler

open Kanren.Data

open FSharp.Quotations

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

    let translateUnifyRhs sourceInfo rhs varset =
            match rhs with
            | ExprShape.ShapeVar v ->
                UnifyRhs.Var v
            | Patterns.Value (value, constType) ->
                UnifyRhs.Constant(value, constType)
            | _ ->
                raise(System.Exception($"Unsupported unify rhs: {rhs}"))

    let rec translateUnify sourceInfo lhs rhs unifyType (varset: VarSet) =
            match lhs with
            | ExprShape.ShapeVar v ->
                ( varset, Unify(v, translateUnifyRhs sourceInfo rhs varset))
            | _ ->
                match rhs with
                | ExprShape.ShapeVar v ->
                    translateUnify sourceInfo rhs lhs unifyType varset
                | _ ->
                    let (varset'', lvar) = varset.newVar(unifyType)
                    let (varset''', rvar) = varset.newVar(unifyType)
                    let rhs1 = translateUnifyRhs sourceInfo lhs varset
                    let rhs2 = translateUnifyRhs sourceInfo rhs varset
                    ( varset''', Conj([initGoal sourceInfo lhs (Unify(lvar, rhs1));
                                        initGoal sourceInfo rhs (Unify(rvar, rhs2));
                                        initGoal sourceInfo lhs (Unify(lvar, UnifyRhs.Var rvar)) ]))


    let translateCallArg sourceInfo (varset: VarSet, extraGoals: Goal list) arg =
            match arg with
            | ExprShape.ShapeVar v ->
                (v, (varset, extraGoals))
            | _ ->
                let (varset', var) = varset.newVar(arg.Type)
                let rhs = translateUnifyRhs sourceInfo arg varset
                (var, (varset', initGoal sourceInfo arg (Unify(var, rhs)) :: extraGoals))

    let translateCallArgs sourceInfo args (varset: VarSet) =
            List.mapFold (translateCallArg sourceInfo) (varset, []) args

    let translateCall sourceInfo callee args (varset: VarSet) =
            let (argVars, (varset', extraGoals)) = translateCallArgs sourceInfo args varset
            let call = initGoal sourceInfo args.Head (Goal.Call(callee, argVars))
            (varset', Conj(List.rev (call :: extraGoals)))

    let rec translateSubExpr existingSourceInfo expr varset =
            let exprSourceInfo = getSourceInfo existingSourceInfo expr
            match expr with
            | DerivedPatterns.SpecificCall (<@@ call @@>) (_, _, [Patterns.PropertyGet (None, prop, _); Patterns.NewTuple (args)] ) ->
                translateCall exprSourceInfo prop args varset
            | DerivedPatterns.SpecificCall (<@@ exists @@>) (_, _, [ExprShape.ShapeLambda (v, expr)] ) ->
                translateSubExpr exprSourceInfo expr varset
            | DerivedPatterns.SpecificCall (<@@ (=) @@>) (_, [unifyType], [lhs; rhs] ) ->
                translateUnify exprSourceInfo lhs rhs unifyType varset
            | DerivedPatterns.AndAlso (condExpr, thenExpr) ->
                let (varset', condGoal) = translateSubExprGoal exprSourceInfo condExpr varset
                let (varset'', thenGoal) = translateSubExprGoal exprSourceInfo thenExpr varset'
                (varset'', Conj([condGoal; thenGoal]))
            | DerivedPatterns.OrElse (condExpr, elseExpr) ->
                let (varset', condGoal) = translateSubExprGoal exprSourceInfo condExpr varset
                let (varset'', elseGoal) = translateSubExprGoal exprSourceInfo elseExpr varset'
                (varset'', Disj([condGoal; elseGoal]))
            | True' _ ->
                (varset, Conj([]))
            | False' _ ->
                (varset, Disj([]))
            | ExprShape.ShapeVar v ->
                raise (System.Exception($"Var {expr.ToString(true)}"))
            | ExprShape.ShapeLambda (v, subExpr) ->
                raise (System.Exception($"Lambda {expr.ToString(true)}"))
            | ExprShape.ShapeCombination (combo, exprs) ->
                raise (System.Exception($"Combo {expr.ToString (true)}"))
    and
        translateSubExprGoal sourceInfo expr varset =
            let (varset', goal) = translateSubExpr sourceInfo expr varset
            (varset', initGoal sourceInfo expr goal)

    let rec translateArgs sourceInfo expr varset =
        let exprSourceInfo = getSourceInfo sourceInfo expr
        match expr with
            | Patterns.Let (_, Patterns.TupleGet (_, _), subExpr) ->
                translateArgs exprSourceInfo subExpr varset
            | _ ->
                translateSubExprGoal exprSourceInfo expr varset

    let translateExpr sourceInfo expr varset =
        let exprSourceInfo = getSourceInfo sourceInfo expr
        match expr with
            | Patterns.Lambda (_, subExpr) -> translateArgs exprSourceInfo subExpr varset
            | _ -> raise (System.Exception($"Expected lambda at top level of clause"))
