namespace Kanren.Data

open FSharp.Quotations

type Goal =
    | Unify of Expr * Expr * System.Type
    | Call of System.Reflection.PropertyInfo * (Expr list)
    | Conj of Goal list
    | Disj of Goal list
    | Exists of Var * Goal
    | Not of Goal

type IRelation = interface
    abstract member GetName: unit -> string
end

type 'A Relation =
    { Name: string; Clauses: (('A -> bool) Expr) list }
    interface IRelation with
        member x.GetName() = x.Name

[<System.AttributeUsage(System.AttributeTargets.Property, AllowMultiple=false)>]
type RelationAttribute(name : string) =
    inherit System.Attribute()

[<AutoOpenAttribute>]
module Bulitins =
    let call (relation:'A Relation) (argument: 'A) = raise (System.Exception("function 'call' should only occur in quotations"))
    let exists (f: Var -> bool) = raise (System.Exception("function 'exists' should only occur in quotations"))
