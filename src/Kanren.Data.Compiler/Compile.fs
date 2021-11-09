namespace Kanren.Data.Compiler

open System.Reflection
open Kanren.Data

module Compile =

    let internal parseRelation
                    (sourceModule: kanrenModule)
                    (rel: RelationAttribute)
                    (relation: RelationBase)
                    (moduleInfo: ModuleInfo) =
        let varset = VarSet.init

        let varset' =
            QuotationParser.getVars varset relation.Body

        let sourceInfo =
            { SourceInfo.File = relation.Path
              StartLine = relation.Line
              EndLine = relation.Line
              StartCol = 0
              EndCol = 0 }

        let parserInfo = ParserInfo.init sourceModule varset' sourceInfo

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
                    initRelation moduleInfo.InstTable sourceModule.moduleName rel relation args goal' parserInfo''.varset

                (moduleInfo.addRelation (relation), parserInfo''.errors)
            | Error modeErrors -> (moduleInfo, List.concat (parserInfo''.errors :: modeErrors))

    let internal compileRelationMethod (instance: kanrenModule) (moduleInfo, errors) (property: PropertyInfo) =
        let relationAttribute =
            property.GetCustomAttribute(typeof<RelationAttribute>) :?> RelationAttribute

        let relation =
            property.GetValue(instance) :?> RelationBase

        do System.Console.WriteLine($"{relation.Body}")

        let (moduleInfo', errors') =
            parseRelation instance relationAttribute relation moduleInfo

        (moduleInfo', errors' :: errors)

    let internal compileKanrenModule (moduleType: System.Type) =
        let moduleInfo = ModuleInfo.init

        let instance =
            System.Activator.CreateInstance(moduleType) :?> kanrenModule

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
