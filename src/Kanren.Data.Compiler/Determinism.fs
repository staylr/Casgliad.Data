namespace Kanren.Data.Compiler

open Kanren.Data

[<AutoOpen>]
module Determinism =
    let detConjunctionMaxSoln s1 s2 =
        match (s1, s2) with
        | (NumSolutions.NoSolutions, _)
        | (NumSolutions.OneSolution, NumSolutions.NoSolutions)
        | (NumSolutions.MoreThanOneSolution, NumSolutions.NoSolutions) ->
            NumSolutions.NoSolutions
        | (NumSolutions.OneSolution, s2) ->
            s2
        | (NumSolutions.CommittedChoice, NumSolutions.MoreThanOneSolution) ->
            raise (System.Exception("committed choice followed by nondet"))
        | (NumSolutions.CommittedChoice, _) ->
            NumSolutions.CommittedChoice
        | (NumSolutions.MoreThanOneSolution, _) ->
            NumSolutions.MoreThanOneSolution

    let detConjunctionCanFail f1 f2 =
        match (f1, f2) with
        | (CanFail, _) -> CanFail
        | (CannotFail, CanFail) -> CanFail
        | (CannotFail, CannotFail) -> CannotFail

    let conjunctionDeterminism det1 det2 =
        let (maxSoln1, canFail1) = determinismComponents det1
        match maxSoln1 with
        | NumSolutions.NoSolutions ->
            det1
        | NumSolutions.OneSolution
        | NumSolutions.MoreThanOneSolution
        | NumSolutions.CommittedChoice ->
            let (maxSoln2, canFail2) = determinismComponents det2
            determinismFromComponents (detConjunctionMaxSoln maxSoln1 maxSoln2)
                                    (detConjunctionCanFail canFail1 canFail2)

    let parallelConjunctionDeterminism det1 det2 =
        let (maxSoln1, canFail1) = determinismComponents det1
        let (maxSoln2, canFail2) = determinismComponents det2
        determinismFromComponents (detConjunctionMaxSoln maxSoln1 maxSoln2)
                                (detConjunctionCanFail canFail1 canFail2)

    let negationDeterminism det =
        match det with
        | Det -> Some Fail
        | Semidet -> Some Semidet
        | Multi -> None
        | CommittedChoiceMulti -> None
        | Nondet -> None
        | CommittedChoiceNondet -> None
        | Erroneous -> Some Erroneous
        | Fail -> Some Det
