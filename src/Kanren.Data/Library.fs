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
                                //fun((a, ( e, ({ Modes = m; Determinism = d }: RelationMode)), c), x, y, z, u) ->
                                fun(x, y, z, u) ->
                                    x = 1
                                    && y = 2
                                    && z = y + 3
                                    && z < 10
                                    && kanren.call(this.rel2, (x, _i()))
                                    && (match u with
                                        | Case1(_, _) -> true
                                        | Case2(_, _) -> false
                                        | Case3(_) -> false)
                            )


        [<Relation>]
        member this.rel4 = relation("rel", [mode [Out; Out; Out; Out; Out] Determinism.Nondet],
                                fun((a, ( e, ({ Modes = m; Determinism = d }: RelationMode)), c), x, y, z, u) ->
                                    x = 1
                                    && y = 2
                                    && z = y + 3
                                    && z < 10
                                    && kanren.call(this.rel2, (x, z))
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
