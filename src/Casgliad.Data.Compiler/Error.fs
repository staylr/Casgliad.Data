namespace Casgliad.Data.Compiler

open FSharp.Quotations

type internal ErrorContext =
    | Goal of Goal
    | Expr of Expr
    | String of string

type internal ErrorSeverity =
    | None = 0
    | Info = 1
    | Warning = 2
    | Error = 3

type internal Error =
    { Text: string
      Location: SourceInfo Option
      Context: ErrorContext
      Severity: ErrorSeverity }

module internal Error =
    let maxSeverity (x: ErrorSeverity) (y: ErrorSeverity) = if (x > y) then x else y

    let maxSeverityOfList errors =
        List.fold (fun max (e1: Error) -> maxSeverity e1.Severity max) ErrorSeverity.None errors

    let unsupportedExpressionError sourceInfo expr =
        { Error.Location = Some sourceInfo
          Text = "Unsupported expression"
          Context = ErrorContext.Expr expr
          Severity = ErrorSeverity.Error }

    let invalidCallee sourceInfo expr =
        { Error.Location = Some sourceInfo
          Text = "expected `this.<property>' in callee of casgliad.call"
          Context = ErrorContext.Expr expr
          Severity = ErrorSeverity.Error }

    let unsupportedUnifyRhsError sourceInfo expr =
        { Error.Location = Some sourceInfo
          Text = "Unsupported unify right-hand-side"
          Context = ErrorContext.Expr expr
          Severity = ErrorSeverity.Error }

    let invalidModeError sourceInfo mode =
        { Text = $"invalid mode {mode}"
          Context = String "mode declaration attribute"
          Location = Some sourceInfo
          Severity = ErrorSeverity.Error }

    let invalidModeListLengthError sourceInfo actual expected =
        { Text = $"incorrect mode list length {actual}, expected {expected}"
          Context = String "mode declaration"
          Location = Some sourceInfo
          Severity = ErrorSeverity.Error }
