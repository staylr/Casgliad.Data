namespace Kanren.Data.Tests

open Swensen.Unquote
open Kanren.Data
open Kanren.Data.Compiler
open NUnit.Framework

module InstTests =
    let instTable = InstTable()

    [<Test>]
    let unifyGroundFree () : unit =
        test <@ instTable.unifyInst(Bound Ground, Free) = Some (Ground, Det) @>

    [<Test>]
    let unifyFreeFreeFails () : unit =
         test <@ instTable.unifyInst(InstE.Free, InstE.Free) = None @>

    [<Test>]
    let unifyFreeGroundCtorSucceeds () : unit =
        let boundInst = BoundCtor ([ { Constructor = Tuple 2; ArgInsts = [Ground; Ground] } ], InstTestResults.noResults)
        test <@ Some (boundInst, Det) = instTable.unifyInst(InstE.Free, Bound boundInst) @>

    [<Test>]
    let unifyIntersectsBoundInsts () : unit =
        let boundInst1 = BoundCtor (
                                    [ { Constructor = Constant(IntValue(1L), typeof<int>); ArgInsts = [] };
                                      { Constructor = Constant(IntValue(2L), typeof<int>); ArgInsts = [] } ],
                                    InstTestResults.noResults)
        let boundInst2 = BoundCtor ([ { Constructor = Constant(IntValue(2L), typeof<int>); ArgInsts = [] };
                                      { Constructor = Constant(IntValue(3L), typeof<int>); ArgInsts = [] } ],
                                    InstTestResults.noResults)
        test <@ instTable.unifyInst(Bound boundInst1, Bound boundInst2) =
                                    Some (BoundCtor (
                                            [ { Constructor = Constant(IntValue(2L), typeof<int>); ArgInsts = [] } ],
                                            InstTestResults.noResults ),
                                        Semidet) @>

    [<Test>]
    let unifyDisjointBoundInstsReturnsNotReached () : unit =
        let boundInst1 = BoundCtor (
                                    [ { Constructor = Constant(IntValue(1L), typeof<int>); ArgInsts = [] };
                                      { Constructor = Constant(IntValue(2L), typeof<int>); ArgInsts = [] } ],
                                    InstTestResults.noResults)
        let boundInst2 = BoundCtor (
                                    [ { Constructor = Constant(IntValue(3L), typeof<int>); ArgInsts = [] };
                                      { Constructor = Constant(IntValue(4L), typeof<int>); ArgInsts = [] } ],
                                    InstTestResults.noResults)
        test <@ instTable.unifyInst(Bound boundInst1, Bound boundInst2) =
                                    Some (NotReached, Fail) @>
