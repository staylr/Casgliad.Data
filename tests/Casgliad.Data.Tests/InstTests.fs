namespace Casgliad.Data.Tests

open System.Collections.Generic
open Swensen.Unquote
open Casgliad.Data
open Casgliad.Data.Compiler
open NUnit.Framework

module InstTests =
    let internal instTable = InstTable ()

    [<Test>]
    let unifyGroundFree () : unit =
        test <@ instTable.unifyInst (Bound Ground, Free) = Some (Ground, Det) @>

    [<Test>]
    let unifyFreeFreeFails () : unit =
        test <@ instTable.unifyInst (InstE.Free, InstE.Free) = None @>

    [<Test>]
    let unifyFreeGroundCtorSucceeds () : unit =
        let boundInst =
            BoundCtor
                { BoundInsts =
                      [ { Constructor = Tuple 2
                          ArgInsts = [ Ground; Ground ] } ]
                  TestResults = InstTestResults.noResults }

        test <@ Some (boundInst, Det) = instTable.unifyInst (InstE.Free, Bound boundInst) @>

    [<Test>]
    let unifyIntersectsBoundInsts () : unit =
        let boundInst1 =
            BoundCtor
                { BoundInsts =
                      [ { Constructor = Constant (IntValue (1L), typeof<int>)
                          ArgInsts = [] }
                        { Constructor = Constant (IntValue (2L), typeof<int>)
                          ArgInsts = [] } ]
                  TestResults = InstTestResults.noResults }

        let boundInst2 =
            BoundCtor
                { BoundInsts =
                      [ { Constructor = Constant (IntValue (2L), typeof<int>)
                          ArgInsts = [] }
                        { Constructor = Constant (IntValue (3L), typeof<int>)
                          ArgInsts = [] } ]
                  TestResults = InstTestResults.noResults }

        test
            <@ instTable.unifyInst (Bound boundInst1, Bound boundInst2) = Some (
                BoundCtor
                    { BoundInsts =
                          [ { Constructor = Constant (IntValue (2L), typeof<int>)
                              ArgInsts = [] } ]
                      TestResults = InstTestResults.groundTestResults },
                Semidet
            ) @>

    [<Test>]
    let unifyDisjointBoundInstsReturnsNotReached () : unit =
        let boundInst1 =
            BoundCtor
                { BoundInsts =
                      [ { Constructor = Constant (IntValue (1L), typeof<int>)
                          ArgInsts = [] }
                        { Constructor = Constant (IntValue (2L), typeof<int>)
                          ArgInsts = [] } ]
                  TestResults = InstTestResults.noResults }

        let boundInst2 =
            BoundCtor
                { BoundInsts =
                      [ { Constructor = Constant (IntValue (3L), typeof<int>)
                          ArgInsts = [] }
                        { Constructor = Constant (IntValue (4L), typeof<int>)
                          ArgInsts = [] } ]
                  TestResults = InstTestResults.noResults }

        test <@ instTable.unifyInst (Bound boundInst1, Bound boundInst2) = Some (NotReached, Fail) @>
