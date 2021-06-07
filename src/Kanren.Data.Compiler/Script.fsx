#r "bin/Debug/net5.0/Kanren.Data.dll"
#r "bin/Debug/net5.0/Kanren.Data.Compiler.dll"

open Kanren.Data
open Kanren.Data.Compiler


let result =
    Kanren.Data.Compiler.Compile.compileKanrenModule typeof<Kanren.Data.Main.kanrenTest>

printfn $"{result}"
