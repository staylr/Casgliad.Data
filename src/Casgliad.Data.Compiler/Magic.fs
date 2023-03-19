module internal Casgliad.Data.Compiler.Magic


type TransformMethod =
    | Magic
    | Context

let magicTransformRule scc conjuncts = []


let magicTransformRules scc disjuncts =
    let (recursiveRules, exitRules) =
        List.partition (goalIsRecursive scc) disjuncts



    []


let magicTransformGoal scc goal =
    match goal.Goal with
    | Disjunction (disjuncts) -> magicTransformRules scc disjuncts
    | _ -> magicTransformRules scc [ goal ]
