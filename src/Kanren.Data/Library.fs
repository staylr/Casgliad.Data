namespace Kanren.Data

open Kanren.Data
open FSharp.Quotations

module Main =

    [<Module("kanren")>]
    type kanrenTest() =
        [<Relation>]
        member this.rel2 = kanren("rel3", [mode [Out; Out] Determinism.Nondet],
                                fun (x, y) -> x = 4 && y = 2)

        [<Relation>]
        member this.rel3 = kanren("rel3", [mode [In; Out] Determinism.Nondet],
                                fun (x, y) -> x = 4 && y = 2)

        [<Relation>]
        [<Mode("out, out", Determinism.Nondet)>]
        member this.rel = kanren("rel", [mode [Out; Out; Out] Determinism.Nondet],
                                fun(x, y, z) ->
                                    x = 1
                                    && y = 2
                                    && z = y + 3
                                    && z < 10
                                    && call this.rel2 (x, z)
                            )


    //[<AbstractClass>]
    //type 'A tree() =
    //    abstract member p : Expr<('A * 'A) -> bool>

    //    member this.anc = <@ fun (x: 'A, y: 'A) ->
    //                        call this.p (x, y)
    //                        || exists(fun z -> call this.p (x, z) && call this.anc (z, y)) @>

    //type concrete() =
    //    inherit tree<int>()

    //    override this.p = <@ fun(x, y) -> x = y @>
