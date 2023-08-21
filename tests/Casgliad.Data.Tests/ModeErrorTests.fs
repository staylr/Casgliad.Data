module Casgliad.Data.Tests.ModeErrorTests

open System
open Swensen.Unquote
open Casgliad.Data
open Casgliad.Data.Compiler
open Casgliad.Data.Tests.CompileTest
open NUnit.Framework


type modeTest1() =
    interface casgliadModule with
        member this.moduleName = "modeTest1"

    [<Relation>]
    member this.rel2 =
        Relation("rel2", [ mode [ Out; Out ] Determinism.Semidet ], (fun (x, y) -> x = 4 && y = 2))

    [<Relation>]
    member this.rel3 =
        Relation("rel3", [ mode [ In; Out ] Determinism.Det ], (fun (x, y) -> x = 4 && y = 2))


[<Test>]
let testDetErrors () : unit =
    let (errors, moduleInfo) =
        Casgliad.Data.Compiler.Compile.compileModule (modeTest1 ())

    test <@ errors.DeterminismErrors.Length = 1 @>
    test <@ errors.DeterminismWarnings.Length = 1 @>
