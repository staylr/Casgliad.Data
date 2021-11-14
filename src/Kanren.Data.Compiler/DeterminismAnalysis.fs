module internal Kanren.Data.Compiler.DeterminismAnalysis

type SolutionContext =
    | FirstSolution
    | AllSolutions


let determinismInferProcedureBody instTable argModes varSet goal lookupRelationModes lookupFSharpModes =

    let rec determinismInferGoal (instMap0: InstMap) (goal: Goal) solutionContext =
        let (solutionContext', addPruning) =
            if (instMap0.hasOutputVars instTable varSet instMap0 goal.Info.NonLocals) then
                (FirstSolution, true)
            else
                (solutionContext, false)

        goal

    goal


