namespace Kanren.Data

open System.Runtime.InteropServices
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

type IRelation = interface
    abstract member getName: unit -> string
end

type 'A Relation =
    { Name: string; Clauses: (('A -> bool) Expr) list }
    interface IRelation with
        member x.getName() = x.Name

[<System.AttributeUsage(System.AttributeTargets.Property, AllowMultiple=false)>]
type RelationAttribute(name : string) =
    inherit System.Attribute()

[<System.AttributeUsage(System.AttributeTargets.Property, AllowMultiple=true)>]
type ModeAttribute(mode: string, [<Optional; DefaultParameterValue(Determinism.Nondet)>] determinism : Determinism) =
    inherit System.Attribute()

[<AutoOpenAttribute>]
module Bulitins =
    let call (relation:'A Relation) (argument: 'A) = raise (System.Exception("function 'call' should only occur in quotations"))
    let exists (f: Var -> bool) = raise (System.Exception("function 'exists' should only occur in quotations"))
    
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
