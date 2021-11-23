namespace Kanren.Data.Compiler

open Kanren.Data

[<AutoOpen>]
module internal Determinism =
    let numSolutions =
        function
        | Determinism.Erroneous -> NoSolutions
        | Determinism.Fail -> NoSolutions
        | Determinism.Det -> OneSolution
        | Determinism.Semidet -> OneSolution
        | Determinism.Multi -> MoreThanOneSolution
        | Determinism.CommittedChoiceMulti -> CommittedChoice
        | Determinism.Nondet -> MoreThanOneSolution
        | Determinism.CommittedChoiceNondet -> CommittedChoice

    let canFail =
        function
        | Determinism.Erroneous -> CannotFail
        | Determinism.Fail -> CanFail
        | Determinism.Det -> CannotFail
        | Determinism.Semidet -> CanFail
        | Determinism.Multi -> CannotFail
        | Determinism.CommittedChoiceMulti -> CannotFail
        | Determinism.Nondet -> CanFail
        | Determinism.CommittedChoiceNondet -> CanFail

    let determinismComponents (d: Determinism) = (numSolutions d, canFail d)

    let determinismFromComponents numSolutions canFail =
        match (numSolutions, canFail) with
        | (NoSolutions, CanFail) -> Fail
        | (NoSolutions, CannotFail) -> Erroneous
        | (OneSolution, CanFail) -> Semidet
        | (OneSolution, CannotFail) -> Det
        | (MoreThanOneSolution, CanFail) -> Nondet
        | (MoreThanOneSolution, CannotFail) -> Multi
        | (CommittedChoice, CanFail) -> CommittedChoiceNondet
        | (CommittedChoice, CannotFail) -> CommittedChoiceMulti

    let detConjunctionMaxSoln s1 s2 =
        match (s1, s2) with
        | (NumSolutions.NoSolutions, _)
        | (NumSolutions.OneSolution, NumSolutions.NoSolutions)
        | (NumSolutions.MoreThanOneSolution, NumSolutions.NoSolutions) -> NumSolutions.NoSolutions
        | (NumSolutions.OneSolution, s2) -> s2
        | (NumSolutions.CommittedChoice, NumSolutions.MoreThanOneSolution) ->
            raise (System.Exception ("committed choice followed by nondet"))
        | (NumSolutions.CommittedChoice, _) -> NumSolutions.CommittedChoice
        | (NumSolutions.MoreThanOneSolution, _) -> NumSolutions.MoreThanOneSolution

    let detConjunctionCanFail f1 f2 =
        match (f1, f2) with
        | (CanFail, _) -> CanFail
        | (CannotFail, CanFail) -> CanFail
        | (CannotFail, CannotFail) -> CannotFail

    let conjunctionDeterminism det1 det2 =
        let (maxSoln1, canFail1) = determinismComponents det1

        match maxSoln1 with
        | NumSolutions.NoSolutions -> det1
        | NumSolutions.OneSolution
        | NumSolutions.MoreThanOneSolution
        | NumSolutions.CommittedChoice ->
            let (maxSoln2, canFail2) = determinismComponents det2

            determinismFromComponents
                (detConjunctionMaxSoln maxSoln1 maxSoln2)
                (detConjunctionCanFail canFail1 canFail2)

    let parallelConjunctionDeterminism det1 det2 =
        let (maxSoln1, canFail1) = determinismComponents det1
        let (maxSoln2, canFail2) = determinismComponents det2
        determinismFromComponents (detConjunctionMaxSoln maxSoln1 maxSoln2) (detConjunctionCanFail canFail1 canFail2)

    let detDisjunctionMaxSoln d1 d2 =
        match d1 with
        | NumSolutions.NoSolutions -> d2
        | NumSolutions.OneSolution ->
            match d2 with
            | NumSolutions.NoSolutions -> NumSolutions.OneSolution
            | NumSolutions.OneSolution -> NumSolutions.MoreThanOneSolution
            | NumSolutions.CommittedChoice -> NumSolutions.CommittedChoice
            | NumSolutions.MoreThanOneSolution -> NumSolutions.MoreThanOneSolution
        | NumSolutions.CommittedChoice -> NumSolutions.CommittedChoice
        | NumSolutions.MoreThanOneSolution ->
            match d2 with
            | NumSolutions.CommittedChoice -> NumSolutions.CommittedChoice
            | _ -> NumSolutions.MoreThanOneSolution

    let detDisjunctionCanFail d1 d2 =
        if (d1 = CanFail.CanFail && d2 = CanFail.CanFail) then
            CanFail.CanFail
        else
            CanFail.CannotFail

    let disjunctionDeterminism det1 det2 =
        let (maxSoln1, canFail1) = determinismComponents det1
        let (maxSoln2, canFail2) = determinismComponents det2
        determinismFromComponents (detDisjunctionMaxSoln maxSoln1 maxSoln2) (detDisjunctionCanFail canFail1 canFail2)

    let detSwitchMaxSoln d1 d2 =
        match d1 with
        | NumSolutions.NoSolutions -> d2
        | NumSolutions.OneSolution ->
            match d2 with
            | NumSolutions.NoSolutions -> NumSolutions.OneSolution
            | NumSolutions.OneSolution -> NumSolutions.OneSolution
            | NumSolutions.CommittedChoice -> NumSolutions.CommittedChoice
            | NumSolutions.MoreThanOneSolution -> NumSolutions.MoreThanOneSolution
        | NumSolutions.CommittedChoice -> NumSolutions.CommittedChoice
        | NumSolutions.MoreThanOneSolution ->
            match d2 with
            | NumSolutions.CommittedChoice -> NumSolutions.CommittedChoice
            | _ -> NumSolutions.MoreThanOneSolution

    let detSwitchCanFail d1 d2 =
        if (d1 = CanFail.CannotFail && d2 = CanFail.CannotFail) then
            CanFail.CannotFail
        else
            CanFail.CanFail

    let switchDeterminism det1 det2 =
        let (maxSoln1, canFail1) = determinismComponents det1
        let (maxSoln2, canFail2) = determinismComponents det2
        determinismFromComponents (detSwitchMaxSoln maxSoln1 maxSoln2) (detSwitchCanFail canFail1 canFail2)

    let negationDeterminism =
        function
        | Det -> Some Fail
        | Semidet -> Some Semidet
        | Multi -> None
        | CommittedChoiceMulti -> None
        | Nondet -> None
        | CommittedChoiceNondet -> None
        | Erroneous -> Some Erroneous
        | Fail -> Some Det

    type SolutionContext =
        | FirstSolution
        | AllSolutions
        with
        static member ofDeterminism det =
            let (maxSoln, _) = determinismComponents det
            if (maxSoln = CommittedChoice) then FirstSolution else AllSolutions

    type DeterminismComparison =
        | FirstTighterThan
        | FirstSameAs
        | FirstLooserThan
        | Incomparable

    type DeterminismComponentComparison =
        | FirstTighterThan
        | FirstSameAs
        | FirstLooserThan

    let compareCanFails canFailA canFailB =
        match (canFailA, canFailB) with
        | (CannotFail, CannotFail) -> FirstSameAs
        | (CannotFail, CanFail) -> FirstTighterThan
        | (CanFail, CannotFail) -> FirstLooserThan
        | (CanFail, CanFail) -> FirstSameAs

    let compareSolutionCount solutionsA solutionsB =
        match (solutionsA, solutionsB) with
        | (NoSolutions, NoSolutions) -> FirstSameAs
        | (NoSolutions, OneSolution) -> FirstTighterThan
        | (NoSolutions, MoreThanOneSolution) -> FirstTighterThan
        | (NoSolutions, CommittedChoice) -> FirstTighterThan

        | (OneSolution, NoSolutions) -> FirstLooserThan
        | (OneSolution, OneSolution) -> FirstSameAs
        | (OneSolution, MoreThanOneSolution) -> FirstTighterThan
        | (OneSolution, CommittedChoice) -> FirstTighterThan

        | (CommittedChoice, NoSolutions) -> FirstLooserThan
        | (CommittedChoice, OneSolution) -> FirstLooserThan
        | (CommittedChoice, MoreThanOneSolution) -> FirstTighterThan
        | (CommittedChoice, CommittedChoice) -> FirstSameAs

        | (MoreThanOneSolution, NoSolutions) -> FirstLooserThan
        | (MoreThanOneSolution, OneSolution) -> FirstLooserThan
        | (MoreThanOneSolution, MoreThanOneSolution) -> FirstSameAs
        | (MoreThanOneSolution, CommittedChoice) -> FirstLooserThan

    let compareDeterminisms detA detB =
        let (solutionsA, canFailA) = determinismComponents detA
        let (solutionsB, canFailB) = determinismComponents detB
        let compareCanFail = compareCanFails canFailA canFailB
        let compareSolutions = compareSolutionCount solutionsA solutionsB

        match compareCanFail with
        | FirstTighterThan ->
            match compareSolutions with
            | FirstTighterThan | FirstSameAs -> DeterminismComparison.FirstTighterThan
            | FirstLooserThan -> DeterminismComparison.Incomparable
        | FirstSameAs ->
            match compareSolutions with
            | FirstTighterThan -> DeterminismComparison.FirstTighterThan
            | FirstSameAs -> DeterminismComparison.FirstSameAs
            | FirstLooserThan -> DeterminismComparison.FirstLooserThan
        | FirstLooserThan ->
            match compareSolutions with
            | FirstTighterThan -> DeterminismComparison.Incomparable
            | FirstSameAs | FirstLooserThan -> DeterminismComparison.FirstLooserThan


