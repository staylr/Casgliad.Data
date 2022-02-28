module internal Casgliad.Data.Compiler.Magic

type IsRecursive =
    | Recursive
    | NotRecursive

type IsNegated =
    | Negated
    | Positive

type IsLinear =
    | NonLinear
    | LeftLinear
    | RightLinear
    | MultiLinear

type Atom =
    | Call of
        callee: RelationProcId *
        IsRecursive *
        IsNegated *
        input: RelationProcId *
        args: VarId list *
        selectProjectCondition: Goal *
        selectProjectOutputs: VarId list
// | Aggregate

type RuleDefinition = Atom list

type RelationInRuleForm =
    { RelationId: RelationId
      OriginalRelationProcId: RelationProcId Option
      Args: VarId list
      ExitRules: RuleDefinition list
      RecursiveRules: RuleDefinition list }

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
