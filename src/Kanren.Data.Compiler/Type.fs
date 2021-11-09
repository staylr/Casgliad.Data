namespace Kanren.Data.Compiler

open FSharp.Reflection
open Kanren.Data

[<AutoOpen>]
module internal Type =
    let tupleConstructor tupleType = Tuple (FSharpType.GetTupleElements(tupleType).Length)

    let caseArgTypes (case: UnionCaseInfo) =
            case.GetFields()
            |> List.ofArray
            |> List.map (fun p -> p.PropertyType)

    let constructorArgTypes (ctor: Constructor) (concreteType: System.Type) =
        match ctor with
        | Constant _ -> []
        | Tuple _ ->
            if (FSharpType.IsTuple concreteType) then
                FSharpType.GetTupleElements concreteType
                |> List.ofArray
            else
                raise (System.ArgumentException($"tuple inst for non-tuple type ${concreteType.Name}"))
        | Record _ ->
            if (FSharpType.IsRecord concreteType) then
                FSharpType.GetRecordFields concreteType
                |> List.ofArray
                |> List.map (fun p -> p.PropertyType)
            else
                raise (System.ArgumentException($"record inst for non-record type ${concreteType.Name}"))
        | UnionCase (case) ->
            if (concreteType.IsAssignableTo(case.DeclaringType)) then
                let concreteCase =
                    if (case.DeclaringType = concreteType) then
                            case
                    else
                        FSharpType.GetUnionCases concreteType
                        |> Array.find (fun e -> e.Name = case.Name)

                caseArgTypes concreteCase
            else
                raise (System.ArgumentException($"invalid union case inst for ${case.Name}: ${concreteType.FullName} is not an instance of ${case.DeclaringType.FullName}"))

    let constructorArity (ctor: Constructor) : int =
        match ctor with
        | Constant _ -> 0
        | Tuple arity -> arity
        | Record recordType -> FSharpType.GetRecordFields recordType |> Array.length
        | UnionCase case -> case.GetFields() |> Array.length

    let allConstructorArgTypesForType instType =
        if (FSharpType.IsTuple instType) then
            let ctor = tupleConstructor instType
            [ (ctor, constructorArgTypes ctor instType) ]
        elif (FSharpType.IsRecord instType) then
            let ctor = (Record instType)
            [ (ctor, constructorArgTypes ctor instType) ]
        elif (FSharpType.IsUnion instType) then
            FSharpType.GetUnionCases instType
            |> Array.map (fun case -> (UnionCase case, caseArgTypes case))
            |> List.ofArray
        else
            []

    // For future CLP implementation.
    let typeIsSolverType t = false
