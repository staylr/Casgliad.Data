namespace Kanren.Data.Tests

open FSharp.Quotations;
open System
open Expecto
open Swensen.Unquote
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
                let ((args, goal), info) = State.run (QuotationParser.translateExpr expr) (newParserInfo expr)

                test <@ info.errors = [] @> 
                test <@
                        match args with
                        | [arg1; arg2] ->
                            arg1.Name = "x" && arg2.Name = "y"
                        | _ ->
                            false
                        @>

                match goal.goal with
                | Conj([{ goal = Unify(var1, Constructor([], Constant(arg1, _))) }; { goal = Unify(var2, Constructor([], Constant(arg2, _))) }]) ->
                    test <@ var1.Name = "x" @>
                    test <@ var2.Name = "y" @>
                    test <@ arg1 = upcast 4 @>
                    test <@ arg2 = upcast 2 @>
                | _ -> raise(Exception($"invalid goal {goal.goal}"))


            testCase "SingleArg" <| fun _ ->
                let expr = <@ fun x -> x = 4  @>
                let ((args, goal), info) = State.run (QuotationParser.translateExpr expr) (newParserInfo expr)

                test <@ info.errors = [] @> 
                test <@
                        match args with
                        | [arg1] ->
                            arg1.Name = "x"
                        | _ ->
                            false
                        @>
                match goal.goal with
                | Unify(var1, Constructor([], Constant(arg1, _))) ->
                    test <@ var1.Name = "x" @>
                    test <@ arg1 = upcast 4 @>
                | _ -> raise(Exception($"invalid goal {goal.goal}"))

            testCase "Match" <| fun _ ->
                let expr = <@ fun (x, y) -> match x with
                                            | Case1(_, _) -> y = "Case1"
                                            | Case2(_, _) -> y = "Case2"
                                            | Case3(_, _) -> y = "Case3" @>
                let ((args, goal), info) = State.run  (QuotationParser.translateExpr expr) (newParserInfo expr)
                test <@ info.errors = [] @> 

                match goal.goal with
                | Disj([disjunct1; disjunct2; disjunct3]) ->
                    let checkDisjunct disjunct =
                        match disjunct.goal with
                        | Conj([{ goal = Unify(lhs, Constructor([_; _], UnionCase(case))) };
                                { goal = Unify(lhs2, Constructor([], Constant(constant, _))) }]) ->
                            test <@ constant = upcast case.Name @>
                        | _ ->
                            raise(Exception($"unexpected disjunct {goal.goal}"))
                    do checkDisjunct disjunct1
                    do checkDisjunct disjunct2
                    do checkDisjunct disjunct3
                | _ -> raise(Exception($"unexpected goal {goal.goal}"))


            testCase "DeconstructTuple" <| fun _ ->
                let expr = <@ fun (x, y) ->
                                    x = 1
                                    && let (a, b) = y in a = b
                                @>
                let ((args, goal), info) = State.run  (QuotationParser.translateExpr expr) (newParserInfo expr)
                test <@ info.errors = [] @>
                test <@
                        match args with
                        | [arg1; arg2] ->
                            arg1.Name = "x" && arg2.Name = "y"
                        | _ ->
                            false
                    @>
                match goal.goal with
                | Conj([{ goal = Unify(var1, Constructor([], Constant(arg1, _))) };
                        { goal = Unify(var2, Constructor([var3; var4], Tuple)) };
                        { goal = Unify(var5, Var(var6)) }]) ->
                    test <@ var1.Name = "x" @>
                    test <@ arg1 = upcast 1 @>
                    test <@ var2.Name = "y" @>
                    test <@ var3.Name = "a" @>
                    test <@ var4.Name = "b" @>
                    test <@ var3 = var5 @>
                    test <@ var4 = var6 @>
                | _ -> raise(Exception($"unexpected goal {goal.goal}"))

            testCase "DeconstructTuple2" <| fun _ ->
                    let expr = <@ fun((a, (e, ({ Modes = m; Determinism = d }: RelationMode)), c), x, y, z, u) ->
                                                        x = 1
                                                        && y = 2
                                                        && z = y + 3
                                                        && z < 10
                                    @>
                    let ((args, goal), info) = State.run  (QuotationParser.translateExpr expr) (newParserInfo expr)
                    Expect.equal (List.length info.errors) 0 "Found errors"

            testCase "Exists" <| fun _ ->
                let expr = <@ fun (x, y) -> kanren.exists(fun z -> x = 4 && y = 2 && z = 3) @>
                let ((args, goal), info) = State.run  (QuotationParser.translateExpr expr) (newParserInfo expr)
                test <@ info.errors = [] @>
                match goal.goal with
                | Conj([{ goal = Unify(var1, Constructor([], Constant(arg1, _))) };
                        { goal = Unify(var2, Constructor([], Constant(arg2, _))) };
                        { goal = Unify(var3, Constructor([], Constant(arg3, _))) }]) ->
                    test <@ var1.Name = "x" @>
                    test <@ var2.Name = "y" @>
                    test <@ var3.Name = "z" @>
                    test <@ arg1 = upcast 4 @>
                    test <@ arg2 = upcast 2 @>
                    test <@ arg3 = upcast 3 @>
                | _ -> raise(Exception($"unexpected goal {goal.goal}"))

            testCase "ExistsTuple" <| fun _ ->
                let expr = <@ fun (x, y) -> kanren.exists(fun (z1, z2) -> x = 4 && y = 2 && z1 = 6 && z2 = 7) @>
                let ((args, goal), info) = State.run  (QuotationParser.translateExpr expr) (newParserInfo expr)
                test <@ info.errors = [] @>
                match goal.goal with
                | Conj([{ goal = Unify(var1, Constructor([], Constant(arg1, _))) };
                        { goal = Unify(var2, Constructor([], Constant(arg2, _))) };
                        { goal = Unify(var3, Constructor([], Constant(arg3, _))) };
                        { goal = Unify(var4, Constructor([], Constant(arg4, _))) }]) ->
                    test <@ var1.Name = "x" @>
                    test <@ var2.Name = "y" @>
                    test <@ var3.Name = "z1" @>
                    test <@ var4.Name = "z2" @>
                    test <@ arg1 = upcast 4 @>
                    test <@ arg2 = upcast 2 @>
                    test <@ arg3 = upcast 6 @>
                    test <@ arg4 = upcast 7 @>
                | _ -> raise(Exception($"unexpected goal {goal.goal}"))

        ]

