namespace Kanren.Data

open Kanren.Data

module Main =

    [<Relation("rel2")>]
    [<Mode("oo", Determinism.Nondet)>]
    let rel2 = { Name = "rel2"; Clauses = [ <@ fun (x, y) -> x = 4 && y = 2 @> ] }

    [<Relation("rel")>]
    let rel = { Name = "rel"; Clauses = [ <@ fun (x, y, z) ->
                                                    (x = 1 && y = 2 && z = y + 3 && z < 10
                                                    && call rel2 (x, z)) @> ] }
