namespace Kanren.Data

open System.Runtime.InteropServices
open System.Runtime.CompilerServices
open FSharp.Quotations

type Inst =
    | Ground
    | Free

type Mode = Inst * Inst

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


type RelationMode = { Modes: Mode list; Determinism: Determinism }

type kanrenBase(name: string, modes: RelationMode list, body: Expr) =
    member this.Name = name
    member this.Modes = modes
    member this.Body = body

type 'A kanren(name: string, modes: RelationMode list, [<ReflectedDefinitionAttribute>]body: Expr<'A -> bool>) =
    inherit kanrenBase(name, modes, body)
    member this.Body = body

[<System.AttributeUsage(System.AttributeTargets.Class, AllowMultiple=false)>]
type ModuleAttribute(name: string, [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
                                            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int) =
    inherit System.Attribute()
    member x.Name = name
    member x.SourcePath = path
    member x.SourceLine = line

[<System.AttributeUsage(System.AttributeTargets.Property, AllowMultiple=false)>]
type RelationAttribute([<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
                                            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int) =
    inherit System.Attribute()
    member x.SourcePath = path
    member x.SourceLine = line

[<System.AttributeUsage(System.AttributeTargets.Property, AllowMultiple=true)>]
type ModeAttribute(mode: string, determinism: Determinism,
                                    [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
                                    [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int) =
    inherit System.Attribute()
    member x.Mode = mode
    member x.Determinism = determinism
    member x.SourcePath = path
    member x.SourceLine = line

[<AutoOpen>]
module Mode =
    let (=>) (inst1: Inst) (inst2: Inst) = (inst1, inst2)

    let In = Ground => Ground
    let Out = Free => Ground

    let mode modes det = { Modes = modes; Determinism = det; }

[<AutoOpen>]
module Bulitins =

    let exists (f: 'A -> bool) = raise (System.Exception("function 'exists' should only occur in quotations"))
    let call (r: 'A kanren) (args: 'A) : bool =  raise (System.Exception("function 'call' should only occur in quotations"))

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
