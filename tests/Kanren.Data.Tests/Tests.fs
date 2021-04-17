namespace Kanren.Data.Tests

open FSharp.Quotations;
open System
open Expecto
open Kanren.Data
open Kanren.Data.Compiler

module QuotationTests =
    let newParserInfo (expr: Expr) =
        let varset = QuotationParser.getVars VarSet.init expr
        let testSourceInfo =
                match (QuotationParser.getSourceInfo expr) with
                | Some sourceInfo -> sourceInfo
                | None -> { SourceInfo.File = "..."; StartLine = 0; EndLine= 0; StartCol = 0; EndCol = 0 }
        ParserInfo.init varset testSourceInfo

    [<Tests>]
    let tests =
        testList "QuotationParser" [
            testCase "Simple" <| fun _ ->
                let expr = <@ fun (x, y) -> x = 4 && y = 2 @>
                let (parserInfo, args, goal) = QuotationParser.translateExpr expr (newParserInfo expr)
                Expect.equal (List.length args) 2 "Found args"
                match goal.goal with
                | Conj([{ goal = Unify(var1, Constant(arg1, _)) }; { goal = Unify(var2, Constant(arg2, _)) }]) ->
                    Expect.equal var1.Name "x" "x"
                    Expect.equal var2.Name "y" "y"
                    Expect.equal arg1 (upcast 4)  "const 1"
                    Expect.equal arg1 (upcast 2) "const 1"
                | _ -> raise(Exception($"invalid goal {goal.goal}"))
        ]
