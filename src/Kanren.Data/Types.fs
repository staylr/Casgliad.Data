namespace Kanren.Data

open System.Runtime.InteropServices
open System.Runtime.CompilerServices
open FSharp.Quotations

type Determinism =
    | Erroneous
    | Fail
    | Det
    | Semidet
    | Multi
    | CommittedChoiceMulti
    | Nondet
    | CommittedChoiceNondet

type NumSolutions =
    | NoSolutions
    | OneSolution
    | MoreThanOneSolution
    | CommittedChoice

type CanFail =
    | CanFail
    | CannotFail

    // We don't enumerate every single size of builtin type. Care must be taken
    // when evaluating at compile time to cast to the correct type first.
type ConstantValue =
    | IntValue of int64
    | UIntValue of uint64
    | DecimalValue of decimal
    | DoubleValue of double
    | BoolValue of bool
    | CharValue of char
    | StringValue of string

type Constructor =
    | Constant of Value: ConstantValue * ConstType: System.Type
    | Tuple of Arity: int
    | Record of System.Type
    | UnionCase of FSharp.Reflection.UnionCaseInfo
    interface System.IComparable with
        member this.CompareTo other =
            match other with
            | :? Constructor as p -> (this :> System.IComparable<_>).CompareTo p
            | _ -> -1

    interface System.IComparable<Constructor> with
        member this.CompareTo other = 0
            (*match this with
            | Constant (constVal, constType) ->
                match other with
                | Constant (otherVal, otherType) ->
                    let res = *)

// TODO: user defined insts, e,g ListSkel.
type Inst =
    | Free
    | Ground
    | Any   // Not yet implemented. For use in constraint programming.
    | HigherOrder of RelationMode
    | Bound of BoundInst list
    | NotReached
and BoundInst = { Constructor: Constructor; ArgInsts: Inst list }
and Mode = Inst * Inst
and RelationMode =
    { Modes: Mode list
      Determinism: Determinism }

[<AbstractClass>]
type RelationBase(name: string, modes: RelationMode list, body: Expr, path: string, line: int) =
    member this.Name = name
    member this.Modes = modes
    member this.Body = body
    member this.Path = path
    member this.Line = line

type 'A Relation
    (
        name: string,
        modes: RelationMode list,
        [<ReflectedDefinitionAttribute>] body: Expr<'A -> bool>,
        [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
        [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
    ) =
    inherit RelationBase(name, modes, body, path, line)
    member this.Body = body

type AggregateFunc =
    | Sum
    | Count
    | Max
    | Min
    | Average
    | StdDev

type Aggregate<'Query, 'Input, 'Res> =
    { Func: AggregateFunc
      Select: ('Query -> 'Input) }

type kanren() =
    static member exists
        (
            f: 'A -> bool,
            [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
        ) : bool =
        raise (System.Exception("'exists' should only occur in quotations"))

    static member call
        (
            r: 'A Relation,
            args: 'A,
            [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
        ) : bool =
        raise (System.Exception("'call' should only occur in quotations"))

    static member groupBy
        (
            f: 'A -> bool,
            groupBy: 'A -> 'G,
            result: 'G * Set<'A>,
            [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
        ) : bool =
        raise (System.Exception("'groupBy' should only occur in quotations"))

    static member aggregate
        (
            query: 'A -> bool,
            groupBy: 'A -> 'G,
            aggregate: Aggregate<'A, 'I, 'Res>,
            groupKey: 'G,
            result: 'Res,
            [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
        ) : bool =
        raise (System.Exception("'aggregate' should only occur in quotations"))

    static member aggregate
        (
            query: 'A -> bool,
            groupBy: 'A -> 'G,
            aggregates: (Aggregate<'A, 'I1, 'Res1> * Aggregate<'A, 'I2, 'Res2>),
            groupKey: 'G,
            result1: 'Res1,
            result2: 'Res2,
            [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
        ) : bool =
        raise (System.Exception("'aggregate' should only occur in quotations"))

    static member count(select: 'Q -> 'I) : Aggregate<'Q, 'I, int> =
        { Func = AggregateFunc.Count
          Select = select }

    static member sum(select: 'Q -> int) : Aggregate<'Q, int, int> =
        { Func = AggregateFunc.Sum
          Select = select }

    // If-then-else with existentially quantified variables scoped across the if-then part.
    static member ifThenElse
        (
            ifThenClause: ('A -> ('A -> bool * 'A -> bool)),
            elseClause: (unit -> bool),
            [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
            [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
        ) : bool =
        raise (System.Exception("'ifThenElse' should only occur in quotations"))

[<System.AttributeUsage(System.AttributeTargets.Property, AllowMultiple = false)>]
type RelationAttribute
    (
        [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
        [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
    ) =
    inherit System.Attribute()
    member x.SourcePath = path
    member x.SourceLine = line

[<System.AttributeUsage(System.AttributeTargets.Class, AllowMultiple = false)>]
type ModuleAttribute
    (
        name: string,
        [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
        [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
    ) =
    inherit System.Attribute()
    member x.Name = name
    member x.SourcePath = path
    member x.SourceLine = line

[<AutoOpen>]
module Mode =
    // Anonymous variable for call arguments.
    // _ only works in pattern matches.
    let _i () : 'A =
        raise (System.Exception("'_i' should only occur in quotations"))

    let (=>) (inst1: Inst) (inst2: Inst) = (inst1, inst2)

    let In = Ground => Ground
    let Out = Free => Ground

    let mode modes det = { Modes = modes; Determinism = det }
