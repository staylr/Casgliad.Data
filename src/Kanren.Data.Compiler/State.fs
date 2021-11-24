namespace Kanren.Data.Compiler

module State =

    type StateFunc<'State, 'T> = 'State -> 'T * 'State

    let inline run (stateFunc: StateFunc<'State, 'T>) initialState = stateFunc initialState

    type StateBuilder() =
        // 'T -> M<'T>
        member inline __.Return value : StateFunc<'State, 'T> = fun state -> value, state

        // M<'T> -> M<'T>
        member inline __.ReturnFrom func : StateFunc<'State, 'T> = func

        // unit -> M<'T>
        member inline this.Zero() : StateFunc<'State, unit> = this.Return ()

        // M<'T> * ('T -> M<'U>) -> M<'U>
        member inline __.Bind(computation: StateFunc<_, 'T>, binder: 'T -> StateFunc<_, _>) : StateFunc<'State, 'U> =
            fun state ->
                let result, state = computation state
                (binder result) state

        // (unit -> M<'T>) -> M<'T>
        member inline this.Delay(generator: unit -> StateFunc<_, _>) : StateFunc<'State, 'T> =
            this.Bind (this.Return (), generator)

        // M<'T> -> M<'T> -> M<'T>
        // or
        // M<unit> -> M<'T> -> M<'T>
        member inline this.Combine(r1: StateFunc<_, _>, r2: StateFunc<_, _>) : StateFunc<'State, 'T> =
            this.Bind (r1, (fun () -> r2))

        // M<'T> * (exn -> M<'T>) -> M<'T>
        member inline __.TryWith
            (
                computation: StateFunc<_, _>,
                catchHandler: exn -> StateFunc<_, _>
            ) : StateFunc<'State, 'T> =
            fun state ->
                try
                    computation state
                with
                | ex -> catchHandler ex state

        // M<'T> * (unit -> unit) -> M<'T>
        member inline __.TryFinally(computation: StateFunc<_, _>, compensation) : StateFunc<'State, 'T> =
            fun state ->
                try
                    computation state
                finally
                    compensation ()

        // 'T * ('T -> M<'U>) -> M<'U> when 'T :> IDisposable
        member this.Using(resource: ('T :> System.IDisposable), binder: 'T -> StateFunc<_, _>) : StateFunc<'State, 'U> =
            fun state ->
                try
                    binder resource state
                finally
                    if not <| isNull (box resource) then
                        resource.Dispose ()

        // (unit -> bool) * M<'T> -> M<'T>
        member this.While(guard, body: StateFunc<'State, unit>) : StateFunc<'State, unit> =
            fun state ->
                let mutable state = state

                while guard () do
                    state <- snd <| body state

                (), state

        // seq<'T> * ('T -> M<'U>) -> M<'U>
        // or
        // seq<'T> * ('T -> M<'U>) -> seq<M<'U>>
        member inline this.For(sequence: seq<_>, body: 'T -> StateFunc<_, _>) : StateFunc<'State, unit> =
            this.Using (
                sequence.GetEnumerator (),
                (fun enum -> this.While (enum.MoveNext, this.Delay (fun () -> body enum.Current)))
            )

module Reader =
    type ReaderFunc<'Env, 'T> = 'Env -> 'T

    /// <summary>
    /// </summary>
    [<Sealed>]
    type ReaderBuilder() =
        // 'T -> M<'T>
        member __.Return value : ReaderFunc<'Env, 'T> = fun _ -> value

        // M<'T> -> M<'T>
        member __.ReturnFrom func : ReaderFunc<'Env, 'T> = func

        // unit -> M<'T>
        member __.Zero() : ReaderFunc<'Env, unit> = fun _ -> ()

        // M<'T> * ('T -> M<'U>) -> M<'U>
        member __.Bind(f: ReaderFunc<_, _>, binder: 'T -> ReaderFunc<_, _>) : ReaderFunc<'Env, 'U> =
            fun env ->
                let result = f env
                binder result env

        // (unit -> M<'T>) -> M<'T>
        member this.Delay(generator: unit -> ReaderFunc<_, _>) : ReaderFunc<'Env, 'T> =
            this.Bind (this.Zero (), generator)

        // M<'T> -> M<'T> -> M<'T>
        // or
        // M<unit> -> M<'T> -> M<'T>
        member this.Combine(r1: ReaderFunc<_, _>, r2: ReaderFunc<_, _>) : ReaderFunc<'Env, 'T> =
            this.Bind (r1, (fun () -> r2))

        // M<'T> * (exn -> M<'T>) -> M<'T>
        member __.TryWith(body: ReaderFunc<_, _>, handler: exn -> ReaderFunc<_, _>) : ReaderFunc<'Env, 'T> =
            fun env ->
                try
                    body env
                with
                | ex -> handler ex env

        // M<'T> * (unit -> unit) -> M<'T>
        member __.TryFinally(body: ReaderFunc<_, _>, handler) : ReaderFunc<'Env, 'T> =
            fun env ->
                try
                    body env
                finally
                    handler ()

        // 'T * ('T -> M<'U>) -> M<'U> when 'T :> IDisposable
        member this.Using(resource: ('T :> System.IDisposable), binder: 'T -> ReaderFunc<_, _>) : ReaderFunc<'Env, 'U> =
            fun env ->
                try
                    binder resource env
                finally
                    if not <| isNull (box resource) then
                        resource.Dispose ()

        // (unit -> bool) * M<'T> -> M<'T>
        member this.While(guard, body: ReaderFunc<_, _>) : ReaderFunc<'Env, unit> =
            fun env ->
                while guard () do
                    body env

        // seq<'T> * ('T -> M<'U>) -> M<'U>
        // or
        // seq<'T> * ('T -> M<'U>) -> seq<M<'U>>
        member this.For(sequence: seq<_>, body: 'T -> ReaderFunc<_, _>) : ReaderFunc<'Env, unit> =
            this.Using (
                sequence.GetEnumerator (),
                fun enum -> this.While (enum.MoveNext, this.Delay (fun () -> body enum.Current))
            )
// OPTIMIZE : Could this be replaced with Seq.map?
(*
            fun env ->
                sequence
                |> Seq.iter (fun el ->
                    body el env)
            *)
