namespace Kanren.Data.Tests

module ExpectoTemplate =

    open Expecto

    [<EntryPoint>]
    let main argv =
        Tests.runTestsInAssembly defaultConfig argv
