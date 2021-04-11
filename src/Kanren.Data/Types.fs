namespace Kanren.Data

open System.Runtime.InteropServices
open System.Runtime.CompilerServices
open FSharp.Quotations

type Determinism =
    | Fail = 0
    | Det = 1
    | Semidet = 2
    | Multi = 3
    | Nondet = 4
    
type NumSolutions =
    | NoSolutions
    | OneSolution
    | MoreThanOneSolution

type CanFail =
    | CanFail
    | CannotFail

[<System.AttributeUsage(System.AttributeTargets.Class, AllowMultiple=false)>]
type ModuleAttribute(name : string, [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
                                            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int) =
    inherit System.Attribute()
    member x.Name = name
    member x.SourcePath = path
    member x.SourceLine = line

[<System.AttributeUsage(System.AttributeTargets.Method, AllowMultiple=false)>]
type RelationAttribute(name : string, [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
                                            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int) =
    inherit System.Attribute()
    member x.Name = name
    member x.SourcePath = path
    member x.SourceLine = line

[<System.AttributeUsage(System.AttributeTargets.Method, AllowMultiple=true)>]
type ModeAttribute(mode: string, determinism: Determinism,
                                    [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
                                    [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int) =
    inherit System.Attribute()
    member x.Mode = mode
    member x.Determinism = determinism
    member x.SourcePath = path
    member x.SourceLine = line

[<AutoOpenAttribute>]
module Bulitins =
    let exists (f: Var -> bool) = raise (System.Exception("function 'exists' should only occur in quotations"))

    let fact (value: 'A) = true

    let numSolutions (d : Determinism) =
        match d with
        | Determinism.Fail -> NoSolutions
        | Determinism.Det -> OneSolution
        | Determinism.Semidet -> OneSolution
        | Determinism.Multi -> MoreThanOneSolution
        | Determinism.Nondet -> MoreThanOneSolution
        | _ -> raise (System.Exception("unknonwn Determinism"))

    let canFail (d : Determinism) =
        match d with
        | Determinism.Fail -> CanFail
        | Determinism.Det -> CannotFail
        | Determinism.Semidet -> CanFail
        | Determinism.Multi -> CannotFail
        | Determinism.Nondet -> CanFail
        | _ -> raise (System.Exception("unknonwn Determinism"))
