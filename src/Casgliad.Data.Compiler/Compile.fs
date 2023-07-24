module internal Casgliad.Data.Compiler.Compile

open System.Reflection
open Casgliad.Data

let internal parseRelation (sourceModule: casgliadModule) (relation: RelationBase) (moduleInfo: ModuleInfo) =
    let varset = VarSet.init

    let varset' = QuotationParser.getVars varset relation.Body

    let sourceInfo: SourceInfo =
        { File = relation.Path
          StartLine = relation.Line
          EndLine = relation.Line
          StartCol = 0
          EndCol = 0 }

    let parserInfo = ParserInfo.init sourceModule varset' sourceInfo

    let ((args, goal: Goal), parserInfo'') =
        State.run (QuotationParser.translateExpr relation.Body) parserInfo

    let goal' = Simplify.simplifyGoal (parserInfo''.varset) goal

    if (Error.maxSeverityOfList parserInfo''.errors = ErrorSeverity.Error) then
        parserInfo''.errors
    else
        let modeResult = List.map (parseModes sourceInfo args) relation.Modes

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

let internal parseRelationMethod (moduleInfo: ModuleInfo) (instance: casgliadModule) errors (property: PropertyInfo) =
    let relationAttribute =
        property.GetCustomAttribute(typeof<RelationAttribute>) :?> RelationAttribute

    let relation = property.GetValue(instance) :?> RelationBase

    do System.Console.WriteLine($"{relation.Body}")

    let errors' = parseRelation instance relation moduleInfo

    errors' :: errors


type CompilationErrors =
    { ParseErrors: Error list
      ModeErrors: ModeErrors.ModeError list
      DeterminismErrors: DeterminismErrors.DeterminismError list }

let internal compileModule (moduleType: System.Type) =
    let moduleInfo = ModuleInfo.init

    let instance = System.Activator.CreateInstance(moduleType) :?> casgliadModule

    let relationProperties =
        moduleType.GetProperties(BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Instance)
        |> Seq.filter (fun (p: PropertyInfo) -> notNull (p.GetCustomAttribute typeof<RelationAttribute>))

    let parseErrors =
        Seq.fold (parseRelationMethod moduleInfo instance) [] relationProperties
        |> List.concat

    let errors =
        if (parseErrors = []) then
            Modecheck.modecheckModule moduleInfo
            (parseErrors, [], [])
        else
            (parseErrors, [], [])

    (errors, moduleInfo)
