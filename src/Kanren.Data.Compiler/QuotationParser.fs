namespace Kanren.Data.Compiler

open Kanren.Data

open FSharp.Quotations

module QuotationParser =

    let getSourceInfo (s:SourceInfo Option) (e:Quotations.Expr) = 
        let (|Val|_|) e : 't option = 
            match e with
            | Quotations.Patterns.Value(:? 't as v,_) -> Some v
            | _ -> None
        let (|Tup|_|) = Quotations.Patterns.(|NewTuple|_|)

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

    let initGoal (sourceInfo:SourceInfo Option) (expr:Expr) (goal:GoalExpr) = { goal = goal; info = GoalInfo.init(getSourceInfo sourceInfo expr) }

    let rec translateSubExpr existingSourceInfo expr =
            let exprSourceInfo = getSourceInfo existingSourceInfo expr

            match expr with
            | DerivedPatterns.SpecificCall (<@@ call @@>) (_, _, [Patterns.PropertyGet (None, prop, _); Patterns.NewTuple (args)] ) ->
                Call (prop, args)
            | DerivedPatterns.SpecificCall (<@@ exists @@>) (_, _, [Patterns.Lambda (v, expr)] ) ->
                translateSubExpr exprSourceInfo expr
            | DerivedPatterns.SpecificCall (<@@ (=) @@>) (_, [optype], [l; r] ) ->
                Unify (l, r, optype)
            | Patterns.IfThenElse (guardExpr, thenExpr, False' _) ->
                Conj ([translateSubExpr exprSourceInfo guardExpr |> initGoal exprSourceInfo guardExpr;
                        translateSubExpr exprSourceInfo thenExpr |> initGoal exprSourceInfo thenExpr]) // desugared &&
            | Patterns.IfThenElse (guardExpr, True' _, elseExpr) ->
                Disj ([translateSubExpr exprSourceInfo guardExpr |> initGoal exprSourceInfo guardExpr;
                        translateSubExpr exprSourceInfo elseExpr |> initGoal exprSourceInfo elseExpr]) // desugared ||
            | ExprShape.ShapeVar v ->
                raise (System.Exception($"Var {expr.ToString(true)}"))
            | ExprShape.ShapeLambda (v, subExpr) ->
                Exists (v, (translateSubExpr exprSourceInfo expr) |> initGoal exprSourceInfo subExpr)
            | ExprShape.ShapeCombination (combo, exprs) ->
                raise (System.Exception($"Combo {expr.ToString (true)}"))

    let rec translateArgs sourceInfo expr =
        let exprSourceInfo = getSourceInfo sourceInfo expr
        match expr with
            | Patterns.Let (_, Patterns.TupleGet (_, _), subExpr) -> translateArgs exprSourceInfo subExpr
            | _ -> initGoal exprSourceInfo expr (translateSubExpr exprSourceInfo expr)

    let translateExpr sourceInfo expr =
        let exprSourceInfo = getSourceInfo sourceInfo expr
        match expr with
            | Patterns.Lambda (_, subExpr) -> translateArgs exprSourceInfo subExpr
            | _ -> raise (System.Exception($"Expected lambda at top level of clause"))
