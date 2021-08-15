namespace Kanren.Data.Tests

open Swensen.Unquote
open Kanren.Data
open Kanren.Data.Compiler
open NUnit.Framework

module InstTests =
    let instTable = InstTable()

    [<Test>]
    let unifyGroundFree () : unit =
        test <@ instTable.unifyInst(InstE.Ground, InstE.Free) = Some (InstE.Ground, Det) @>

    [<Test>]
    let unifyFreeFreeFails () : unit =
         test <@ instTable.unifyInst(InstE.Free, InstE.Free) = None @>

    [<Test>]
    let unifyFreePartialCtorFails () : unit =
        test <@ None = instTable.unifyInst(InstE.Free, InstE.Bound (InstTestResults.noResults,
                                            [ { Constructor = Tuple 2; ArgInsts = [InstE.Free; InstE.Ground] } ])) @>

    [<Test>]
    let unifyFreeGroundCtorSucceeds () : unit =
        let boundInst = InstE.Bound (InstTestResults.noResults, [ { Constructor = Tuple 2; ArgInsts = [InstE.Ground; InstE.Ground] } ] )
        test <@ Some (boundInst, Det) = instTable.unifyInst(InstE.Free, boundInst) @>
