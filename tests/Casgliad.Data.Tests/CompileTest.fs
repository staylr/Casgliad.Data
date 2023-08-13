module Casgliad.Data.Tests.CompileTest

open FSharp.Quotations
open Casgliad.Data
open Casgliad.Data.Compiler
open Swensen.Unquote

let defaultSourceInfo =
    { SourceInfo.File = "..."
      StartLine = 0
      EndLine = 0
      StartCol = 0
      EndCol = 0 }

let internal newParserInfo (expr: Expr) (moduleToCompile: casgliadModule) =
    let varset = QuotationParser.getVars VarSet.init expr

    let testSourceInfo =
        match (QuotationParser.getSourceInfo expr) with
        | Some sourceInfo -> sourceInfo
        | None -> defaultSourceInfo

    ParserInfo.init moduleToCompile varset testSourceInfo

let internal testGoalInfo
    (info: ParserInfo)
    goalInfo
    (nonLocalNames: string list)
    (determinism: Determinism)
    (instMapDelta: (string * BoundInstE) list)
    =
    let nonLocals =
        nonLocalNames
        |> List.map (fun v -> info.varset.findByName(v).Id)
        |> TagSet.ofList

    test <@ goalInfo.NonLocals = nonLocals @>

    let mappings = goalInfo.InstMapDelta.mappings ()

    instMapDelta
    |> List.iter (fun (varName, expectedInst) ->
        let var = info.varset.findByName(varName).Id
        let mappingInst = mappings.[var]
        test <@ mappingInst = expectedInst @>)

    mappings
    |> Map.iter (fun varId _ ->
        let var = info.varset.[varId]

        if (not (List.exists (fun (varName, _) -> varName = var.Name) instMapDelta)) then
            failwith $"unexpected mapping for {var.Name}")

    test <@ goalInfo.Determinism = determinism @>


let internal compileExpr expr maybeArgModes moduleToCompile lookupRelationModes =
    let ((args, goal), info) =
        State.run (QuotationParser.translateExpr expr) (newParserInfo expr moduleToCompile)

    let (goal', varset) = Quantification.implicitlyQuantifyGoal args info.varset goal

    let (argModes, det) =
        match maybeArgModes with
        | Some(argModes, det) -> (argModes, det)
        | None -> (args |> List.map (fun _ -> (InstE.Free, BoundInstE.Ground)), Nondet)

    let instTable = InstTable()

    let relationProcId =
        ({ RelationId.ModuleName = "mod"
           RelationId.RelationName = UserRelation "pred" },
         0<procIdMeasure>)

    let (goal'', modeErrors, modeWarnings, _, varset') =
        Modecheck.modecheckBodyGoal
            relationProcId
            varset
            args
            argModes
            instTable
            lookupRelationModes
            Builtins.lookupFSharpFunctionModes
            goal'

    let (goal''', detErrors, detWarnings, inferredDet) =
        if (modeErrors = []) then
            DeterminismAnalysis.determinismInferProcedureBody
                instTable
                relationProcId
                args
                argModes
                det
                varset
                goal''
                lookupRelationModes
                Builtins.lookupFSharpFunctionModes
        else
            (goal'', [], [], det)

    ((args, goal'''), { info with varset = varset' })
