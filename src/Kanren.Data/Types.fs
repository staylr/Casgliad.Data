namespace Kanren.Data

open System.Runtime.InteropServices
open System.Runtime.CompilerServices
open FSharp.Quotations

type Inst =
    | Ground
    | Free

type Mode = Inst * Inst

type Determinism =
    | Erroneous = 0
    | Fail = 1
    | Det = 2
    | Semidet = 3
    | Multi = 4
    | Nondet = 5

type NumSolutions =
    | NoSolutions
    | OneSolution
    | MoreThanOneSolution

type CanFail =
    | CanFail
    | CannotFail

type RelationMode =
    { Modes: Mode list
      Determinism: Determinism }

[<AbstractClass>]
type relationBase(name: string, modes: RelationMode list, body: Expr, path: string, line: int) =
    member this.Name = name
    member this.Modes = modes
    member this.Body = body
    member this.Path = path
    member this.Line = line

type 'A relation
    (
        name: string,
        modes: RelationMode list,
        [<ReflectedDefinitionAttribute>] body: Expr<'A -> bool>,
        [<CallerFilePath; Optional; DefaultParameterValue("")>] path: string,
        [<CallerLineNumber; Optional; DefaultParameterValue(0)>] line: int
    ) =
    inherit relationBase(name, modes, body, path, line)
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
            r: 'A relation,
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
    // Ignore for relation arguments.
    // _ doesn't work because calls are not pattern matches.
    let _i () : 'A =
        raise (System.Exception("'_i' should only occur in quotations"))

    let (=>) (inst1: Inst) (inst2: Inst) = (inst1, inst2)

    let In = Ground => Ground
    let Out = Free => Ground

    let mode modes det = { Modes = modes; Determinism = det }

    let numSolutions (d: Determinism) =
        match d with
        | Determinism.Fail -> NoSolutions
        | Determinism.Det -> OneSolution
        | Determinism.Semidet -> OneSolution
        | Determinism.Multi -> MoreThanOneSolution
        | Determinism.Nondet -> MoreThanOneSolution
        | _ -> raise (System.Exception("unknonwn Determinism"))

    let canFail (d: Determinism) =
        match d with
        | Determinism.Fail -> CanFail
        | Determinism.Det -> CannotFail
        | Determinism.Semidet -> CanFail
        | Determinism.Multi -> CannotFail
        | Determinism.Nondet -> CanFail
        | _ -> raise (System.Exception("unknonwn Determinism"))
