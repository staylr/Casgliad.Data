namespace Kanren.Data.Compiler

[<AutoOpen>]
module Util =

    type SourceInfo = { File: string; StartLine: int; StartCol: int; EndLine: int; EndCol: int }

    let notNull x = match x with | null -> false | _ -> true

    let flip f x y = f y x

    let flipRes f x y =
        let (r, s) = f y x
        (s, r)

    let combineResults (results: List<Result<'a, 'b>>): Result<List<'a>, List<'b>> =
        let rec _combine (ok: List<'a>) (err: List<'b>) (res: List<Result<'a, 'b>>) =
            res |> List.tryHead
            |> function
            | None -> (ok, err)
            | Some curr ->
                match curr with
                | Ok x -> _combine (List.append [x] ok) err (List.tail res)
                | Error e -> _combine ok (List.append [e] err) (List.tail res)
        // Invoke recursive call
        _combine [] [] results
        |> function
           | (values, []) -> Ok values
           | (_, errors) -> Error errors
