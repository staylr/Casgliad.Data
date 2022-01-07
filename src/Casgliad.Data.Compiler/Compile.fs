namespace Casgliad.Data.Compiler

open System.Reflection
open Casgliad.Data

module Compile =

    let internal parseRelation (sourceModule: casgliadModule) (relation: RelationBase) (moduleInfo: ModuleInfo) =
        let varset = VarSet.init

        let varset' =
            QuotationParser.getVars varset relation.Body

        let sourceInfo =
            { SourceInfo.File = relation.Path
              StartLine = relation.Line
              EndLine = relation.Line
              StartCol = 0
              EndCol = 0 }

        let parserInfo =
            ParserInfo.init sourceModule varset' sourceInfo

        let ((args, goal: Goal), parserInfo'') =
            State.run (QuotationParser.translateExpr relation.Body) parserInfo

        let goal' =
            Simplify.simplifyGoal (parserInfo''.varset) goal

        if (Error.maxSeverityOfList parserInfo''.errors = ErrorSeverity.Error) then
            parserInfo''.errors
        else
            let modeResult =
                List.map (parseModes sourceInfo args) relation.Modes

            match combineResults modeResult with
            | Ok _ ->
                let relation =
                    initRelation
                        moduleInfo.InstTable
                        sourceModule.moduleName
                        sourceInfo
                        relation
                        args
                        goal'
                        parserInfo''.varset

                moduleInfo.addRelation (relation)
                parserInfo''.errors
            | Error modeErrors -> List.concat (parserInfo''.errors :: modeErrors)

    let internal compileRelationMethod
        (moduleInfo: ModuleInfo)
        (instance: casgliadModule)
        errors
        (property: PropertyInfo)
        =
        let relationAttribute =
            property.GetCustomAttribute (typeof<RelationAttribute>) :?> RelationAttribute

        let relation =
            property.GetValue (instance) :?> RelationBase

        do System.Console.WriteLine ($"{relation.Body}")

        let errors' =
            parseRelation instance relation moduleInfo

        errors' :: errors

    let internal compileCasgliadModule (moduleType: System.Type) =
        let moduleInfo = ModuleInfo.init

        let instance =
            System.Activator.CreateInstance (moduleType) :?> casgliadModule

        let bindingFlags =
            BindingFlags.Public
            ||| BindingFlags.NonPublic
            ||| BindingFlags.Instance

        let properties =
            moduleType.GetProperties (bindingFlags)
            |> Array.toList

        let relationProperties =
            properties
            |> List.filter (fun (p: PropertyInfo) -> notNull (p.GetCustomAttribute typeof<RelationAttribute>))

        let result =
            List.fold (compileRelationMethod moduleInfo instance) [] relationProperties

        (result, moduleType)
