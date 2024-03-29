namespace Casgliad.Data.Compiler

type SourceInfo =
    { File: string
      StartLine: int
      StartCol: int
      EndLine: int
      EndCol: int }

    static member empty =
        { File = ""
          StartLine = 0
          StartCol = 0
          EndLine = 0
          EndCol = 0 }

    member this.isEmpty() = this.File = ""


[<AutoOpen>]
module internal Util =

    let notNull x =
        match x with
        | null -> false
        | _ -> true

    let flip f x y = f y x

    let swap (x, y) = (y, x)

    let flipRes f x y =
        let (r, s) = f y x
        (s, r)

    let combineResults (results: List<Result<'a, 'b>>) : Result<List<'a>, List<'b>> =
        let rec _combine (ok: List<'a>) (err: List<'b>) (res: List<Result<'a, 'b>>) =
            res
            |> List.tryHead
            |> function
                | None -> (ok, err)
                | Some curr ->
                    match curr with
                    | Ok x -> _combine (List.append [ x ] ok) err (List.tail res)
                    | Error e -> _combine ok (List.append [ e ] err) (List.tail res)
        // Invoke recursive call
        _combine [] [] results
        |> function
            | (values, []) -> Ok values
            | (_, errors) -> Error errors

    /// The function creates a function that calls the argument 'f'
    /// only once and stores the result in a mutable dictionary (cache)
    /// Repeated calls to the resulting function return cached values.
    let memoize f =
        // Create (mutable) cache that is used for storing results of
        // for function arguments that were already calculated.
        let cache = new System.Collections.Generic.Dictionary<_, _>()

        (fun x ->
            // The returned function first performs a cache lookup
            let succ, v = cache.TryGetValue(x)

            if succ then
                v
            else
                // If value was not found, calculate & cache it
                let v = f (x)
                cache.Add(x, v)
                v)

    let rec mapOption (f: 'T -> 'U option) (list: 'T list) : ('U list) option =
        match list with
        | [] -> Some []
        | x :: xs ->
            f x
            |> Option.bind (fun x' -> mapOption f xs |> Option.map (fun xs' -> x' :: xs'))

    let rec foldOption (f: 'S -> 'T -> 'S option) (state: 'S) (list: 'T list) : 'S option =
        match list with
        | [] -> Some state
        | x :: xs ->
            match f state x with
            | None -> None
            | Some state' -> foldOption f state' xs

    let rec foldOption2 (f: 'S -> 'T -> 'U -> 'S option) (state: 'S) (list1: 'T list) (list2: 'U list) : 'S option =
        match (list1, list2) with
        | ([], []) -> Some state
        | (x :: xs, y :: ys) ->
            match f state x y with
            | None -> None
            | Some state' -> foldOption2 f state' xs ys
        | ([], _ :: _)
        | (_ :: _, []) -> failwith "length mismatch in Util.foldOption2"

    let rec mapFoldOption (f: 'S -> 'T -> ('U * 'S) option) (state: 'S) (list: 'T list) : ('U list * 'S) option =
        match list with
        | [] -> Some([], state)
        | x :: xs ->
            match f state x with
            | None -> None
            | Some(x', state') -> mapFoldOption f state' xs |> Option.map (fun res -> (x' :: fst res, snd res))


    let consOption (o: 'T option) (l: 'T list) : 'T list = Option.fold (fun l' o' -> o' :: l') l o

    let rec forall3 (f: 'T -> 'U -> 'V -> bool) (ts: 'T list) (us: 'U list) (vs: 'V list) : bool =
        match (ts, us, vs) with
        | ([], [], []) -> true
        | (t1 :: ts', u1 :: us', v1 :: vs') -> f t1 u1 v1 && forall3 f ts' us' vs'
        | _ -> false


    let rec mapWithState f list =
        Casgliad.Data.Compiler.State.StateBuilder() {
            match list with
            | [] -> return []
            | x :: xs ->
                let! x' = f x
                let! xs' = mapWithState f xs
                return x' :: xs'
        }

    let rec iterWithState f list =
        Casgliad.Data.Compiler.State.StateBuilder() {
            match list with
            | [] -> return ()
            | x :: xs ->
                let! _ = f x
                return! iterWithState f xs
        }

    let rec foldWithState2 f state list =
        Casgliad.Data.Compiler.State.StateBuilder() {
            match list with
            | [] -> return state
            | x :: xs ->
                let! state' = f x state
                return! foldWithState2 f state' xs
        }

    let rec iterWithState2 f list1 list2 =
        Casgliad.Data.Compiler.State.StateBuilder() {
            match (list1, list2) with
            | ([], []) -> return ()
            | (x :: xs, y :: ys) ->
                do! f x y
                return! iterWithState2 f xs ys
            | _ -> failwith "iterWithState2: mismatching lengths"
        }

    let applyRenaming (substitution: Map<'T, 'T>) (mustRename: bool) (var: 'T) =
        if (mustRename) then
            substitution.[var]
        else
            substitution.TryFind(var) |> Option.defaultValue var
