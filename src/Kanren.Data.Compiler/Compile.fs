namespace Kanren.Data.Compiler

open System.Reflection
open FSharp.Quotations
open Kanren.Data

module Compile =

    let internal parseRelation (rel: RelationAttribute) (relation: relationBase) (moduleInfo: ModuleInfo) =
        let varset = VarSet.init

        let varset' =
            QuotationParser.getVars varset relation.Body

        let sourceInfo =
            { SourceInfo.File = relation.Path
              StartLine = relation.Line
              EndLine = relation.Line
              StartCol = 0
              EndCol = 0 }

        let parserInfo = ParserInfo.init varset' sourceInfo

        let ((args, goal: Goal), parserInfo'') =
            State.run (QuotationParser.translateExpr relation.Body) parserInfo

        let goal' = Simplify.simplifyGoal goal

        if (Error.maxSeverityOfList parserInfo''.errors = ErrorSeverity.Error) then
            (moduleInfo, parserInfo''.errors)
        else
            let sourceInfo = relationSourceInfo rel

            let modeResult =
                List.map (parseModes sourceInfo args) relation.Modes

            match combineResults modeResult with
            | Ok _ ->
                let relation =
                    initRelation rel relation args goal' parserInfo''.varset

                (moduleInfo.addRelation (relation), parserInfo''.errors)
            | Error modeErrors -> (moduleInfo, List.concat (parserInfo''.errors :: modeErrors))

    let compileRelationMethod (instance: obj) (moduleInfo, errors) (property: PropertyInfo) =
        let relationAttribute =
            property.GetCustomAttribute(typeof<RelationAttribute>) :?> RelationAttribute

        let relation =
            property.GetValue(instance) :?> relationBase

        do System.Console.WriteLine($"{relation.Body}")

        let (moduleInfo', errors') =
            parseRelation relationAttribute relation moduleInfo

        (moduleInfo', errors' :: errors)

    let compileKanrenModule (moduleType: System.Type) =
        let moduleInfo = ModuleInfo.init

        let instance =
            System.Activator.CreateInstance(moduleType)

        let bindingFlags =
            BindingFlags.Public
            ||| BindingFlags.NonPublic
            ||| BindingFlags.Instance

        let properties =
            moduleType.GetProperties(bindingFlags)
            |> Array.toList

        let relationProperties =
            properties
            |> List.filter (fun (p: PropertyInfo) -> notNull (p.GetCustomAttribute typeof<RelationAttribute>))

        let result =
            List.fold (compileRelationMethod instance) (moduleInfo, []) relationProperties

        (result, moduleType)
