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

    let compileRelationMethod (moduleInfo, errors) (method: MethodInfo) =
             let relationAttribute = method.GetCustomAttribute(typeof<RelationAttribute>) :?> RelationAttribute
             let sourceInfo = relationSourceInfo relationAttribute
             let modeAttributes = method.GetCustomAttributes(typeof<ModeAttribute>) |> Seq.map (fun x -> x :?> ModeAttribute) |> Seq.toList
             let expr = Expr.TryGetReflectedDefinition method
             match expr with
             | Some relationExpr ->
                 do
                    System.Console.WriteLine($"{relationExpr}")
                 let (moduleInfo', errors') = parseRelation relationAttribute modeAttributes relationExpr moduleInfo
                 (moduleInfo', errors' :: errors)
             | None ->
                 let error = { Text = "missing ReflectedDefinitionAttribute"; Location = Some sourceInfo; Context = ErrorContext.String "RelationAttribute"; Severity = ErrorSeverity.Error }
                 (moduleInfo, [error] :: errors)

    let compileKanrenModule (moduleType : System.Type) =
        let moduleInfo = ModuleInfo.init
        
        let bindingFlags = BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Static

        let methods = moduleType.GetMethods(bindingFlags) |> Array.toList
        let relationMethods = methods |> List.filter (fun (p : MethodInfo) -> notNull (p.GetCustomAttribute typeof<RelationAttribute>))
     
        let result = List.fold compileRelationMethod (moduleInfo, []) relationMethods
        (result, moduleType)
