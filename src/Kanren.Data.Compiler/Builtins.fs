namespace Kanren.Data.Compiler

open Kanren.Data.Compiler.ModeInfo

module internal Builtins =
    let lookupFSharpFunctionModes (methodInfo: System.Reflection.MethodInfo) : FunctionModeInfo list =
        let arity = methodInfo.GetParameters().Length
        let modes =
            seq { 1 .. arity }
            |> Seq.map (fun _ -> (Bound Ground, Ground))
            |> List.ofSeq

        [ {
            Method = methodInfo
            ProcId = 1<procIdMeasure>
            Modes = { Modes = modes; Determinism = Kanren.Data.Determinism.Det }
            ResultMode = (Free, Ground) } ]
