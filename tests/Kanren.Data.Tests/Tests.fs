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

    type Union =
    | Case1 of x: int * y: int
    | Case2 of a: int * b: int
    | Case3 of c: int * d: int

    [<Tests>]
    let tests =
        testList "QuotationParser" [
            testCase "Simple" <| fun _ ->
                let expr = <@ fun (x, y) -> x = 4 && y = 2 @>
                let ((args, goal), info) = QuotationParser.run (QuotationParser.translateExpr expr) (newParserInfo expr) 
                Expect.equal (List.length info.errors) 0 "Found errors"
                Expect.equal (List.length args) 2 "Found args"
                match goal.goal with
                | Conj([{ goal = Unify(var1, Constructor([], Constant(arg1, _))) }; { goal = Unify(var2, Constructor([], Constant(arg2, _))) }]) ->
                    Expect.equal var1.Name "x" "x"
                    Expect.equal var2.Name "y" "y"
                    Expect.equal arg1 (upcast 4) "const 1"
                    Expect.equal arg2 (upcast 2) "const 2"
                | _ -> raise(Exception($"invalid goal {goal.goal}"));

            testCase "Match" <| fun _ ->
                let expr = <@ fun (x, y) -> match x with
                                            | Case1(_, _) -> y = "Case1"
                                            | Case2(_, _) -> y = "Case2"
                                            | Case3(_, _) -> y = "Case3" @>
                let ((args, goal), info) = QuotationParser.run  (QuotationParser.translateExpr expr) (newParserInfo expr)
                Expect.equal (List.length info.errors) 0 "Found errors"

                match goal.goal with
                | Disj([disjunct1; disjunct2; disjunct3]) ->
                    let checkDisjunct disjunct =
                        match disjunct.goal with
                        | Conj([{ goal = Unify(lhs, Constructor([_; _], UnionCase(case))) };
                                { goal = Unify(lhs2, Constructor([], Constant(constant2, _))) }]) ->
                            Expect.equal constant2 (upcast case.Name) "case"
                        | _ ->
                            raise(Exception($"unexpected disjunct {goal.goal}"))
                    checkDisjunct disjunct1
                    checkDisjunct disjunct2
                    checkDisjunct disjunct3

                | _ -> raise(Exception($"unexpected goal {goal.goal}"));

            testCase "DeconstructTuple" <| fun _ ->
                        let expr = <@ fun (x, y, z, u) ->
                                           x = 1
                                           && y = 2
                                           && z = y + 3
                                           && z < 10
                                           && let (a, b) = u in a = b
                                        @>
                        let ((args, goal), info) = QuotationParser.run  (QuotationParser.translateExpr expr) (newParserInfo expr)
                        Expect.equal (List.length info.errors) 0 "Found errors"

            testCase "DeconstructTuple2" <| fun _ ->
                           let expr = <@ fun((a, ( e, ({ Modes = m; Determinism = d }: RelationMode)), c), x, y, z, u) ->
                                                             x = 1
                                                             && y = 2
                                                             && z = y + 3
                                                             && z < 10
                                           @>
                           let ((args, goal), info) = QuotationParser.run  (QuotationParser.translateExpr expr) (newParserInfo expr)
                           Expect.equal (List.length info.errors) 0 "Found errors"
        ]

