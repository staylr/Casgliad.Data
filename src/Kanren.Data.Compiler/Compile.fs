namespace Kanren.Data.Compiler

open System.Reflection
open FSharp.Quotations
open Kanren.Data

module Compile =

    let internal parseRelation (rel: RelationAttribute) (modes: ModeAttribute list) (expr : Expr) (moduleInfo: ModuleInfo) =
        let varset = VarSet.init
        let varset' = QuotationParser.getVars varset expr
        let parserInfo = { varset = varset'; errors = [] }
        let (parserInfo'', args, goal) = QuotationParser.translateExpr None expr parserInfo
        let goal' = Simplify.simplifyGoal goal
        if (Error.maxSeverityOfList parserInfo''.errors = ErrorSeverity.Error) then
            (moduleInfo, parserInfo''.errors)
        else
            let sourceInfo = relationSourceInfo rel
            let modeResult = List.map (parseModes sourceInfo args) modes
            match combineResults modeResult with
            | Ok _ ->
                let relation = initRelation rel modes args goal' parserInfo''.varset
                (moduleInfo.addRelation(relation), parserInfo''.errors)
            | Error modeErrors ->
                (moduleInfo, List.concat (parserInfo''.errors :: modeErrors))

    let compileRelationMethod (instance: obj) (moduleInfo, errors) (property: PropertyInfo) =
            let relationAttribute = property.GetCustomAttribute(typeof<RelationAttribute>) :?> RelationAttribute
            let sourceInfo = relationSourceInfo relationAttribute
            let modeAttributes = property.GetCustomAttributes(typeof<ModeAttribute>) |> Seq.map (fun x -> x :?> ModeAttribute) |> Seq.toList
            let expr = property.GetValue(instance) :?> Expr;
            do
                System.Console.WriteLine($"{expr}")

            let (moduleInfo', errors') = parseRelation relationAttribute modeAttributes expr moduleInfo
            (moduleInfo', errors' :: errors)

    let compileKanrenModule (moduleType : System.Type) =
        let moduleInfo = ModuleInfo.init

        let instance = System.Activator.CreateInstance(moduleType)
        
        let bindingFlags = BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Instance

        let properties = moduleType.GetProperties(bindingFlags) |> Array.toList
        let relationProperties = properties |> List.filter (fun (p : PropertyInfo) -> notNull (p.GetCustomAttribute typeof<RelationAttribute>))
     
        let result = List.fold (compileRelationMethod instance) (moduleInfo, []) relationProperties
        (result, moduleType)
