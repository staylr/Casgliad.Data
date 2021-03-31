namespace Kanren.Data

open Kanren.Data

open FSharp.Quotations

module QuotationParser =

    let sourceInfo (e:Quotations.Expr) = 
        let (|Val|_|) e : 't option = 
            match e with
            | Quotations.Patterns.Value(:? 't as v,_) -> Some v
            | _ -> None
        let (|Tup|_|) = Quotations.Patterns.(|NewTuple|_|)

        e.CustomAttributes
        |> List.tryPick (function | Tup [Val("DebugRange")
                                         Tup [Val(file:string)
                                              Val(startLine:int) 
                                              Val(startCol:int)
                                              Val(endLine:int)
                                              Val(endCol:int)]] 
                                      -> Some(file,startLine,startCol,endLine,endCol) 
                                  | _ -> None)

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

    let rec translateSubExpr expr =
        match expr with
        | DerivedPatterns.SpecificCall ( <@@ call @@> ) (_, _, [Patterns.PropertyGet(None, prop, _); Patterns.NewTuple (args)] ) -> Goal.Call (prop, args)
        | DerivedPatterns.SpecificCall ( <@@ (=) @@> ) (_, [optype], [l; r] ) -> Goal.Unify (l, r, optype)
        | Patterns.IfThenElse (guardExpr, thenExpr, False' _)  -> Conj ([translateSubExpr guardExpr; translateSubExpr thenExpr]) // desugared &&
        | Patterns.IfThenElse (guardExpr, True' _, elseExpr)  -> Disj ([translateSubExpr guardExpr; translateSubExpr elseExpr]) // desugared ||
        | ExprShape.ShapeVar v -> raise (System.Exception($"Var {expr.ToString(true)}"))
        | ExprShape.ShapeLambda (v, expr) -> Goal.Exists (v, translateSubExpr(expr))
        | ExprShape.ShapeCombination (combo, exprs) -> raise (System.Exception($"Combo {expr.ToString (true)}"))

    let rec translateArgs expr =
        match expr with
            | Patterns.Let (var, Patterns.TupleGet (_, _), subExpr) -> translateArgs subExpr
            | _ -> translateSubExpr expr

    let translateExpr expr =
        match expr with
            | Patterns.Lambda (_, subExpr) -> translateArgs subExpr
            | _ -> raise (System.Exception($"Expected lambda at top level of clause"))
