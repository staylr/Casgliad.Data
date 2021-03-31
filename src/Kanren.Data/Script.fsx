#r "bin/Debug/net5.0/Kanren.Data.dll"
open Kanren.Data

let g = Kanren.Data.Main.rel.Clauses.Head
printfn $"{g.CustomAttributes}"
printfn $"{g.ToString (true)}"

let x = Kanren.Data.QuotationParser.translateExpr  g
printfn $"{(x.ToString ())}"




