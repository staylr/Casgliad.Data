#r "bin/Debug/net5.0/Kanren.Data.dll"
#r "bin/Debug/net5.0/Kanren.Data.Compiler.dll"
open Kanren.Data
open Kanren.Data.Compiler



let g = Kanren.Data.Main.rel.Clauses.Head
printfn $"{g.CustomAttributes.Head}"
printfn $"{QuotationParser.getSourceInfo  None g.CustomAttributes.Head}"
//printfn $"{g.ToString (true)}"

let x = Kanren.Data.Compiler.QuotationParser.translateExpr None g { ParserInfo.varset = VarSet.init; ParserInfo.errors = [] }
printfn $"{(x.ToString ())}"




