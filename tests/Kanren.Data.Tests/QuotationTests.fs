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

    [<ReflectedDefinitionAttribute>]
    let testVarName info var varName = info.varset.[var].Name = varName

    let compileExpr expr =
        let ((args, goal), info) = State.run (QuotationParser.translateExpr expr) (newParserInfo expr)
        let (goal', varset) = Quantification.implicitlyQuantifyGoal args info.varset goal
        ((args, goal'), { info with varset = varset })

    [<Tests>]
    let tests =
        testList "QuotationParser" [
            testCase "Simple" <| fun _ ->
                let expr = <@ fun (x, y) -> x = 4 && y = 2 @>
                let ((args, goal), info) = compileExpr expr

                test <@ info.errors = [] @> 
                test <@
                        match args with
                        | [arg1; arg2] ->
                            testVarName info arg1 "x" && testVarName info arg2 "y"
                        | _ ->
                            false
                        @>

                match goal.Goal with
                | Conj([{ Goal = Unify(var1, Constructor(Constant(arg1, _), [], _, _), _, _) };
                        { Goal = Unify(var2, Constructor(Constant(arg2, _), [], _, _), _, _) }]) ->
                    test <@ testVarName info var1 "x" @>
                    test <@ testVarName info var2 "y" @>
                    test <@ arg1 = upcast 4 @>
                    test <@ arg2 = upcast 2 @>
                | _ -> raise(Exception($"invalid goal {goal.Goal}"))


            testCase "SingleArg" <| fun _ ->
                let expr = <@ fun x -> x = 4  @>
                let ((args, goal), info) = compileExpr expr

                test <@ info.errors = [] @> 
                test <@
                        match args with
                        | [arg1] ->
                           testVarName info arg1 "x" 
                        | _ ->
                            false
                        @>
                match goal.Goal with
                | Unify(var1, Constructor(Constant(arg1, _), [], _, _), _, _) ->
                    test <@ testVarName info var1 "x" @>
                    test <@ arg1 = upcast 4 @>
                | _ -> raise(Exception($"invalid goal {goal.Goal}"))

            testCase "Match" <| fun _ ->
                let expr = <@ fun (x, y) -> match x with
                                            | Case1(a, b) -> a = b && y = "Case1"
                                            | Case2(c, d) -> c = d && y = "Case2"
                                            | Case3(e, f) -> e = f && y = "Case3" @>
                let ((args, goal), info) = compileExpr expr
                test <@ info.errors = [] @> 

                match goal.Goal with
                | Disj([disjunct1; disjunct2; disjunct3]) ->
                    let checkDisjunct disjunct =
                        match disjunct.Goal with
                        | Conj([
                                { Goal = Unify(lhs, Constructor(UnionCase(case), [_; _], _, _), _, _) };
                                { Goal = Unify(lhsd, Constructor( UnionCase(cased), [_; _], _, _), _, _) };
                                { Goal = Unify(lhst, Var(rhst, _), _, _) };
                                { Goal = Unify(lhs2, Constructor(Constant(constant, _), [], _, _), _, _) }]) ->
                            test <@ constant = upcast case.Name @>
                        | _ ->
                            raise(Exception($"unexpected disjunct {goal.Goal}"))
                    do checkDisjunct disjunct1
                    do checkDisjunct disjunct2
                    do checkDisjunct disjunct3
                | _ -> raise(Exception($"unexpected goal {goal.Goal}"))


            testCase "DeconstructTuple" <| fun _ ->
                let expr = <@ fun (x, y) ->
                                    x = 1
                                    && let (a, b) = y in a = b
                                @>
                let ((args, goal), info) = compileExpr expr
                test <@ info.errors = [] @>
                test <@
                        match args with
                        | [arg1; arg2] ->
                            testVarName info arg1 "x" && testVarName info arg2 "y"
                        | _ ->
                            false
                    @>
                match goal.Goal with
                | Conj([{ Goal = Unify(var1, Constructor(Constant(arg1, _), [], _, _), _, _) };
                        { Goal = Unify(var2, Constructor(Tuple, [var3; var4], _, _), _, _) };
                        { Goal = Unify(var5, Var(var6, _), _, _) }]) ->
                    test <@ testVarName info var1 "x" @>
                    test <@ arg1 = upcast 1 @>
                    test <@ testVarName info var2 "y" @>
                    test <@ testVarName info var3 "a" @>
                    test <@ testVarName info var4 "b" @>
                    test <@ var3 = var5 @>
                    test <@ var4 = var6 @>
                | _ -> raise(Exception($"unexpected goal {goal.Goal}"))

            testCase "DeconstructTuple2" <| fun _ ->
                    let expr = <@ fun (
                                        (a, (e, { Modes = m; Determinism = d }: RelationMode), c),
                                        x) ->
                                                        x = e
                                                        && a = c
                                                        && m = []
                                                        && d = Determinism.Det
                                    @>
                    let ((args, goal), info) = compileExpr expr
                    test <@ info.errors = [] @>
                    match goal.Goal with
                    | Conj([{ Goal = Unify(arg1, Constructor(Tuple, [arga; argeModes1; argc], _, _), _, _) };
                            { Goal = Unify(argeModes2, Constructor(Tuple, [arge; argModes1], _, _), _, _) };
                            { Goal = Unify(argModes2, Constructor(Record(relationModeType), [argm; argd], _, _), _, _) };
                            { Goal = Unify(argx2, Var(arge2, _), _, _) };
                            { Goal = Unify(arga2, Var(argc2, _), _, _) };
                            { Goal = Unify(argm2, Constructor(UnionCase(listEmptyCase), [], _, _), _, _) };
                            { Goal = Unify(argd2, Constructor(Constant(determinismDet, determinismType), [], _, _), _, _) }]) ->
                        test <@ testVarName info arga "a" @>
                        test <@ arg1 = args.[0] @>
                        test <@ testVarName info argc "c" @>
                        test <@ argeModes1 = argeModes2 @>
                        test <@ argModes1 = argModes2 @>
                        test <@ testVarName info arge "e" @>
                        test <@ testVarName info argd "d" @>
                        test <@ testVarName info argm "m" @>
                        test <@ testVarName info argx2 "x" @>
                        test <@ arge2 = arge @>
                        test <@ arga2 = arga @>
                        test <@ argm2 = argm @>
                        test <@ argc2 = argc @>
                        test <@ argd2 = argd @>
                        test <@ listEmptyCase.Name = "Empty" @>
                        test <@ relationModeType.Name = "RelationMode" @>
                        test <@ determinismDet = upcast Determinism.Det @>
                        test <@ determinismType.Name = "Determinism" @>
                    | _ -> raise(Exception($"unexpected goal {goal.Goal}"))

            testCase "Exists" <| fun _ ->
                let expr = <@ fun (x, y) -> kanren.exists(fun z -> x = 4 && y = 2 && z = 3) @>
                let ((args, goal), info) = compileExpr expr
                test <@ info.errors = [] @>
                match goal.Goal with
                | Conj([{ Goal = Unify(var1, Constructor(Constant(arg1, _), [], _, _), _, _) };
                        { Goal = Unify(var2, Constructor(Constant(arg2, _), [], _, _), _, _) };
                        { Goal = Unify(var3, Constructor(Constant(arg3, _), [], _, _), _, _) }]) ->
                    test <@ testVarName info var1 "x" @>
                    test <@ testVarName info var2 "y" @>
                    test <@ testVarName info var3 "z" @>
                    test <@ arg1 = upcast 4 @>
                    test <@ arg2 = upcast 2 @>
                    test <@ arg3 = upcast 3 @>
                | _ -> raise(Exception($"unexpected goal {goal.Goal}"))

            testCase "ExistsTuple" <| fun _ ->
                let expr = <@ fun (x, y) -> kanren.exists(fun (z1, z2) -> x = 4 && y = 2 && z1 = 6 && z2 = 7) @>
                let ((args, goal), info) = compileExpr expr
                test <@ info.errors = [] @>
                match goal.Goal with
                | Conj([{ Goal = Unify(var1, Constructor(Constant(arg1, _), [], _, _), _, _) };
                        { Goal = Unify(var2, Constructor(Constant(arg2, _), [], _, _), _, _) };
                        { Goal = Unify(var3, Constructor(Constant(arg3, _), [], _, _), _, _) };
                        { Goal = Unify(var4, Constructor(Constant(arg4, _), [], _, _), _, _) }]) ->
                    test <@ testVarName info var1 "x" @>
                    test <@ testVarName info var2 "y" @>
                    test <@ testVarName info var3 "z1" @>
                    test <@ testVarName info var4 "z2" @>
                    test <@ arg1 = upcast 4 @>
                    test <@ arg2 = upcast 2 @>
                    test <@ arg3 = upcast 6 @>
                    test <@ arg4 = upcast 7 @>
                | _ -> raise(Exception($"unexpected goal {goal.Goal}"))

        ]

