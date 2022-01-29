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
        VarId list *
        selectProjectCondition: Goal
// | Aggregate

type RuleDefinition =
    { PreCondition: Goal list
      Atoms: Atom list }

type Rule =
    | ExitRule of RuleDefinition
    | RecursiveRule of IsLinear * RuleDefinition

let magicTransformGoal goal = goal
