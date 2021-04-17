namespace Kanren.Data

open Kanren.Data
open FSharp.Quotations

module Main =

    type Union =
    | Case1 of x: int * y: int
    | Case2 of a: int * b: int
    | Case3 of c: int
    
    [<Module("kanren")>]
    type kanrenTest() =
        [<Relation>]
        member this.rel2 = relation("rel3", [mode [Out; Out] Determinism.Nondet],
                                fun (x, y) -> x = 4 && y = 2)

        [<Relation>]
        member this.rel3 = relation("rel3", [mode [In; Out] Determinism.Nondet],
                                fun (x, y) -> x = 4 && y = 2)

        [<Relation>]
        member this.rel = relation("rel", [mode [Out; Out; Out; Out] Determinism.Nondet],
                                fun((a, ( e, ({ Modes = m; Determinism = d }: RelationMode)), c), x, y, z, u) ->
                                    x = 1
                                    && y = 2
                                    && z = y + 3
                                    && z < 10
                                    && kanren.call(this.rel2, (x, z))
                                    && (match u with
                                        | Case1(x1, y1) when x1 = 1 -> x1 * y1 = 2
                                        | Case2(a1, b1) -> a1 * b1 = 3
                                        | _ -> false)
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
