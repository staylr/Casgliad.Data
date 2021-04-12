namespace Kanren.Data

open Kanren.Data

module Main =

    [<Module("kanren")>]
    type kanren() =
        [<Relation("rel2")>]
        [<Mode("out, out", Determinism.Nondet)>]
        member this.rel2 = <@ fun (x, y) -> x = 4 && y = 2 @>

        [<Relation("rel")>]
        [<Mode("out, out", Determinism.Nondet)>]
        member this.rel = <@  fun(x, y, z) ->
                            x = 1
                            && y = 2
                            && z = y + 3
                            && z < 10
                            && call this.rel2 (x, z) @>
