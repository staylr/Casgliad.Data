namespace Kanren.Data

open Kanren.Data

module Main =
    [<Module("kanren")>]
    type kanren =
        [<ReflectedDefinition>]
        [<Relation("rel2")>]
        [<Mode("out, out", Determinism.Nondet)>]
        static member rel2(x, y) = x = 4 && y = 2

        [<ReflectedDefinition>]
        [<Relation("rel")>]
        [<Mode("out, out", Determinism.Nondet)>]
        static member rel(x, y, z) =
                        x = 1
                        && y = 2
                        && z = y + 3
                        && z < 10
                        && kanren.rel2(x, z)
