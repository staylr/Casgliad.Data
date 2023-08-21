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
      ModeErrors: ModeErrors.ModeErrorInfo list
      ModeWarnings: ModeErrors.ModeWarningInfo list
      DeterminismErrors: DeterminismErrors.DeterminismErrorInfo list
      DeterminismWarnings: DeterminismErrors.DeterminismWarningInfo list }

let internal compileModule (instance: casgliadModule) =
    let moduleInfo = ModuleInfo.init

    let relationProperties =
        instance
            .GetType()
            .GetProperties(BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.Instance)
        |> Seq.filter (fun (p: PropertyInfo) -> notNull (p.GetCustomAttribute typeof<RelationAttribute>))

    let parseErrors =
        Seq.fold (parseRelationMethod moduleInfo instance) [] relationProperties
        |> List.concat

    let (modeErrors, modeWarnings) =
        if (parseErrors = []) then
            Modecheck.modecheckModule moduleInfo
        else
            ([], [])

    let (determinismErrors, determinismWarnings) =
        if (parseErrors = [] && modeErrors = []) then
            DeterminismAnalysis.determinismInferModule moduleInfo
        else
            ([], [])

    let errors =
        { ParseErrors = parseErrors
          ModeErrors = modeErrors
          ModeWarnings = modeWarnings
          DeterminismErrors = determinismErrors
          DeterminismWarnings = determinismWarnings }

    (errors, moduleInfo)

let internal compileModuleFromType (moduleType: System.Type) =
    let instance = System.Activator.CreateInstance(moduleType) :?> casgliadModule
    compileModule
