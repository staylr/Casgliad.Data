namespace Casgliad.Data.Compiler

open Casgliad.Data
open Casgliad.Data.Compiler.State
open FSharp.Reflection
open FSharp.Quotations
open FSharp.Collections

type internal ParserInfo =
    { sourceModule: casgliadModule
      varset: VarSet
      errors: Error list
      sourceInfo: SourceInfo }

    member x.newVar(varType) =
        let (varset', var) = x.varset.newVar (varType)
        ({ x with varset = varset' }, var.Id)

    member x.newQVar(var) =
        let (varset', var) = x.varset.addQuotationVar (var)
        ({ x with varset = varset' }, var.Id)

    member x.newError(error) = { x with errors = error :: x.errors }

    static member init sourceModule varset sourceInfo =
        { sourceModule = sourceModule
          varset = varset
          errors = []
          sourceInfo = sourceInfo }

module internal QuotationParser =

    type ParserStateFunc<'T> = StateFunc<ParserInfo, 'T>

    let parse = StateBuilder()

    let getSourceInfo (e: Quotations.Expr) =
        match e with
        | DerivedPatterns.SpecificCall (<@@ casgliad.exists @@>) (_,
                                                                  _,
                                                                  [ _
                                                                    DerivedPatterns.String(file)
                                                                    DerivedPatterns.Int32(line) ])
        | DerivedPatterns.SpecificCall (<@@ casgliad.call @@>) (_,
                                                                _,
                                                                [ _
                                                                  _
                                                                  DerivedPatterns.String(file)
                                                                  DerivedPatterns.Int32(line) ]) ->
            Some
                { SourceInfo.File = file
                  StartLine = line
                  StartCol = 0
                  EndLine = line
                  EndCol = 0 }
        | _ -> None

    let updateSourceInfo expr parserInfo =
        ((),
         match (getSourceInfo expr) with
         | Some sourceInfo ->
             { parserInfo with
                 ParserInfo.sourceInfo = sourceInfo }
         | None -> parserInfo)

    let currentSourceInfo (parserInfo: ParserInfo) = (parserInfo.sourceInfo, parserInfo)

    let getSourceModule (parserInfo: ParserInfo) = (parserInfo.sourceModule, parserInfo)

    let newVar varType (parserInfo: ParserInfo) =
        let (parserInfo', var) = parserInfo.newVar (varType)
        (var, parserInfo')

    let newQVar var (parserInfo: ParserInfo) =
        let (parserInfo', v) = parserInfo.newQVar (var)
        (v, parserInfo')

    let newVars varTypes (parserInfo: ParserInfo) =
        let (vars, parserInfo') =
            List.mapFold (fun (p: ParserInfo) (t: System.Type) -> swap (p.newVar (t))) parserInfo varTypes

        (vars, parserInfo')

    let newError error (parserInfo: ParserInfo) =
        let parserInfo' = parserInfo.newError (error)
        ((), parserInfo')

    let (|True'|_|) expr =
        match expr with
        | Patterns.Value(o, t) when t = typeof<bool> && (o :?> bool) = true -> Some expr
        | _ -> None

    let (|False'|_|) expr =
        match expr with
        | Patterns.Value(o, t) when t = typeof<bool> && (o :?> bool) = false -> Some expr
        | _ -> None

    let rec getVars (varset: VarSet) expr =
        match expr with
        | ExprShape.ShapeVar v -> varset.addQuotationVar (v) |> fst
        | ExprShape.ShapeLambda(v, subExpr) -> getVars (varset.addQuotationVar v |> fst) subExpr
        | ExprShape.ShapeCombination(combo, exprs) -> List.fold getVars varset exprs

    let initGoal (sourceInfo: SourceInfo) (goal: GoalExpr) =
        { Goal = goal
          Info = GoalInfo.init (sourceInfo) }

    let initUnify lhs rhs context =
        Unify(lhs, rhs, ((InstE.Free, BoundInstE.NotReached), (InstE.Free, BoundInstE.NotReached)), context)

    let listToGoal (goals: Goal list) =
        match goals with
        | [ goal ] -> goal.Goal
        | _ -> Conjunction(goals)

    let addCtorSubContext unifyContext ctor index =
        { unifyContext with
            SubContext =
                { Functor = FunctorConstructor(ctor)
                  ArgIndex = index }
                :: unifyContext.SubContext }

    let addCallSubContext unifyContext ctor index =
        { unifyContext with
            SubContext =
                { Functor = FunctorCall(ctor)
                  ArgIndex = index }
                :: unifyContext.SubContext }

    let translateConstant (value: obj) (valueType: System.Type) : ConstantValue =
        if
            valueType = typeof<sbyte>
            || valueType = typeof<int16>
            || valueType = typeof<int>
            || valueType = typeof<int64>
        then
            IntValue(System.Convert.ToInt64(value))
        elif
            valueType = typeof<byte>
            || valueType = typeof<uint16>
            || valueType = typeof<uint>
            || valueType = typeof<uint64>
        then
            UIntValue(System.Convert.ToUInt64(value))
        elif valueType = typeof<decimal> then
            DecimalValue(value :?> decimal)
        elif valueType = typeof<double> then
            DoubleValue(value :?> double)
        elif valueType = typeof<float> then
            DoubleValue(value :?> float)
        elif valueType = typeof<string> then
            StringValue(value :?> string)
        elif valueType = typeof<char> then
            CharValue(value :?> char)
        elif valueType = typeof<bool> then
            BoolValue(value :?> bool)
        else
            raise (System.InvalidOperationException($"Invalid constant {value} of type {valueType.Name}"))

    let makeCtorRhs ctor args =
        UnifyRhs.Constructor(ctor, args, VarCtorUnifyType.Construct, [], CanFail)

    let rec translateUnifyRhs rhs (maybeLhsVar: VarId option) (context: UnifyContext) =
        parse {
            let! sourceInfo = currentSourceInfo

            match rhs with
            | ExprShape.ShapeVar v ->
                let! var = newQVar v
                return ([], Some(UnifyRhs.Var(var, VarVarUnifyType.Assign)))
            | Patterns.Value(value, constType) ->
                return ([], Some(makeCtorRhs (Constant(translateConstant value constType, constType)) []))
            | Patterns.NewTuple(args) ->
                let! (argVars, extraGoals) =
                    translateCallArgs false args (addCtorSubContext context (Tuple(args.Length)))

                return (extraGoals, Some(makeCtorRhs (Tuple(args.Length)) argVars))
            | Patterns.NewRecord(recordType, args) ->
                let! (argVars, extraGoals) =
                    translateCallArgs false args (addCtorSubContext context (Record(recordType)))

                return (extraGoals, Some(makeCtorRhs (Record(recordType)) argVars))
            | Patterns.NewUnionCase(caseInfo, args) ->
                let! (argVars, extraGoals) =
                    translateCallArgs false args (addCtorSubContext context (UnionCase(caseInfo)))

                return (extraGoals, Some(makeCtorRhs (UnionCase(caseInfo)) argVars))
            | Patterns.Call(None, callee, args) ->
                let! (argVars, extraGoals) = translateCallArgs false args (addCallSubContext context callee)

                let! returnVar =
                    match maybeLhsVar with
                    | Some lhsVar -> parse { return lhsVar }
                    | None -> newVar callee.ReturnType

                let goal = FSharpCall((callee, invalidProcId), Some returnVar, argVars)

                return
                    List.append extraGoals [ initGoal sourceInfo goal ],
                    Some(UnifyRhs.Var(returnVar, VarVarUnifyType.Assign))
            | _ ->
                do! newError (Error.unsupportedExpressionError sourceInfo rhs)
                return ([], None)
        }

    and translateCallArg allowDuplicateArgs (seenArgs: Var Set) (extraGoals: Goal list) arg unifyContext =
        parse {
            let! sourceInfo = currentSourceInfo

            match arg with
            | ExprShape.ShapeVar v when not (allowDuplicateArgs && seenArgs.Contains(v)) ->
                let! var = newQVar v
                return (var, seenArgs.Add(v), extraGoals)
            | DerivedPatterns.SpecificCall (<@@ Casgliad.Data.Mode._i @@>) (_, _, _) ->
                // Special syntax to ignore relation arguments.
                let! var = newVar arg.Type
                return (var, seenArgs, extraGoals)
            | _ ->
                let! var = newVar arg.Type
                let! (extraGoals', rhsResult) = translateUnifyRhs arg None unifyContext

                match rhsResult with
                | Some rhs ->
                    return (var, seenArgs, initGoal sourceInfo (initUnify var rhs unifyContext) :: extraGoals')
                | None -> return (var, seenArgs, extraGoals')
        }

    and translateCallArgs' allowDuplicateArgs (argVars, seenArgs, extraGoals) args index constructContext =
        parse {
            match args with
            | [] -> return (argVars, seenArgs, extraGoals)
            | arg :: otherArgs ->
                let! (argVar, seenArgs', extraGoals') =
                    translateCallArg allowDuplicateArgs seenArgs extraGoals arg (constructContext index)

                return!
                    translateCallArgs'
                        allowDuplicateArgs
                        (argVar :: argVars, seenArgs', extraGoals')
                        otherArgs
                        (index + 1)
                        constructContext
        }

    and translateCallArgs allowDuplicateArgs args constructContext =
        parse {
            let! (argVars, _, extraGoals) =
                translateCallArgs' allowDuplicateArgs ([], Set.empty, []) args 1 constructContext

            return (List.rev argVars, extraGoals)
        }

    let translateCall (calleeModule: Expr) (callee: System.Reflection.PropertyInfo) args =
        let rec extractCalleeModule
            (sourceModule: casgliadModule)
            (calleeModuleExpr: Expr)
            (callee: System.Reflection.PropertyInfo)
            : (casgliadModule * obj) option =
            match calleeModuleExpr with
            | Patterns.ValueWithName(_, _, "this") -> Some(sourceModule, callee.GetValue(sourceModule))
            | Patterns.PropertyGet(Some calleeSubExpr, property, []) ->
                extractCalleeModule sourceModule calleeSubExpr property
                |> Option.map (fun (_, innerModule) -> (innerModule :?> casgliadModule, callee.GetValue(innerModule)))
            | _ -> None

        parse {
            let! sourceInfo = currentSourceInfo
            let! sourceModule = getSourceModule

            let maybeCalledRelation = extractCalleeModule sourceModule calleeModule callee

            match maybeCalledRelation with
            | Some(calledModule, calledRelationObj) ->
                try
                    let calledRelation = calledRelationObj :?> RelationBase

                    let calledRelationId =
                        { ModuleName = calledModule.moduleName
                          RelationName = UserRelation calledRelation.Name }

                    let! (argVars, extraGoals) =
                        translateCallArgs false args (fun index ->
                            initUnifyContext (CallArgUnify(RelationCallee(calledRelationId), index)))


                    let call =
                        initGoal sourceInfo (Goal.Call((calledRelationId, invalidProcId), argVars))

                    return listToGoal (List.rev (call :: extraGoals))
                with _ ->
                    do! newError (Error.invalidCallee sourceInfo calleeModule)
                    return Disjunction([])
            | None ->
                do! newError (Error.invalidCallee sourceInfo calleeModule)
                return Disjunction([])
        }

    let rec translateUnify lhs rhs unifyType unifyContext =
        parse {
            let! sourceInfo = currentSourceInfo
            let! (extraGoals1, rhsResult1) = translateUnifyRhs lhs None unifyContext

            let lhsVar =
                match rhsResult1 with
                | Some(UnifyRhs.Var(v, _)) -> Some v
                | _ -> None

            let! (extraGoals2, rhsResult2) = translateUnifyRhs rhs lhsVar unifyContext

            match (rhsResult1, rhsResult2) with
            | (Some rhs1, Some rhs2) ->
                match rhs1 with
                | UnifyRhs.Var(v, _) ->
                    return
                        listToGoal (
                            List.concat
                                [ extraGoals1
                                  extraGoals2
                                  [ initGoal sourceInfo (initUnify v rhs2 unifyContext) ] ]
                        )
                | _ ->
                    match rhs2 with
                    | UnifyRhs.Var(v, _) ->
                        return
                            listToGoal (
                                List.concat
                                    [ extraGoals1
                                      extraGoals2
                                      [ initGoal sourceInfo (initUnify v rhs1 unifyContext) ] ]
                            )
                    | _ ->
                        let! unifyVar = newVar unifyType

                        return
                            listToGoal (
                                List.concat
                                    [ extraGoals1
                                      extraGoals2
                                      [ initGoal sourceInfo (initUnify unifyVar rhs1 unifyContext)
                                        initGoal sourceInfo (initUnify unifyVar rhs2 unifyContext) ] ]
                            )
            | _ ->
                // error.
                return Conjunction(List.append extraGoals1 extraGoals2)
        }

    let unsupportedExpression (expr: Expr) =
        parse {
            let! sourceInfo = currentSourceInfo
            do! newError (Error.unsupportedExpressionError sourceInfo expr)
            return Disjunction([])
        }

    // Some dumpster diving to convert if-then-elses corresponding to source-level pattern matches
    // back into a disjunction. This can only be done where the disjuncts are mutually exclusive.
    let rec unionMatch seenCases exprToTest expr : Option<(Constructor * Expr) list * bool> =
        match expr with
        | Patterns.IfThenElse(Patterns.UnionCaseTest(caseExprToTest, case), thenExpr, elseExpr) when
            exprToTest = caseExprToTest
            ->
            let unionMatchResult = unionMatch (case :: seenCases) exprToTest elseExpr

            match unionMatchResult with
            | Some result -> Some((UnionCase(case), thenExpr) :: fst result, snd result)
            | None ->
                match elseExpr with
                | False' _ ->
                    let allCases = FSharp.Reflection.FSharpType.GetUnionCases(case.DeclaringType)

                    let missingCases = Array.filter (fun c -> not (List.contains c seenCases)) allCases

                    let canFail = missingCases.Length > 1
                    Some([ (UnionCase(case), thenExpr) ], canFail)
                | _ ->
                    let allCases = FSharp.Reflection.FSharpType.GetUnionCases(case.DeclaringType)

                    let missingCases =
                        Array.filter (fun c -> not (List.contains c (case :: seenCases))) allCases

                    if (Array.length missingCases = 1) then
                        Some([ (UnionCase(case), thenExpr); (UnionCase(missingCases.[0]), elseExpr) ], false)
                    else
                        None
        | _ -> None

    let (|UnionMatch|_|) expr : Option<Expr * (Constructor * Expr) list * bool> =
        match expr with
        | Patterns.IfThenElse(Patterns.UnionCaseTest(exprToTest, _), _, _) ->
            match (unionMatch [] exprToTest expr) with
            | Some(cases, canFail) -> Some(exprToTest, cases, canFail)
            | None -> None
        | _ -> None

    // More dumpster diving to recognise chains of tuple, record or union case deconstruction.
    let rec (|Deconstruct|_|) expr : Option<((Var * Expr) list * Expr)> =
        match expr with
        | Patterns.Let(var, getExpr, subExpr) ->
            match getExpr with
            | Patterns.TupleGet(_, _)
            | Patterns.PropertyGet(_, _, _) ->
                match subExpr with
                | Deconstruct(getExprs, bottomSubExpr) -> Some((var, getExpr) :: getExprs, bottomSubExpr)
                | _ -> Some([ (var, getExpr) ], subExpr)
            | _ -> None
        | _ -> None

    type DeconstructUnifyArg = ((Expr * Var Option) Option)
    type DeconstructVar = Expr * Constructor * DeconstructUnifyArg array * System.Type array
    type AssignedDeconstructVar = VarId * Expr * Constructor * VarId list
    type DeconstructVars = List<DeconstructVar>

    let rec deconstructExprEqual ex1 ex2 =
        match (ex1, ex2) with
        | (Patterns.TupleGet(tuple1, tupleIndex1), Patterns.TupleGet(tuple2, tupleIndex2)) ->
            tupleIndex1 = tupleIndex2 && deconstructExprEqual tuple1 tuple2
        | (Patterns.PropertyGet(Some term1, property1, []), Patterns.PropertyGet(Some term2, property2, [])) ->
            property1 = property2 && deconstructExprEqual term1 term2
        | (ExprShape.ShapeVar(v1), ExprShape.ShapeVar(v2)) -> v1 = v2
        | _ -> false

    let deconstructExprMatch ex1 ex2 =
        match (ex1, ex2) with
        | (Patterns.TupleGet(tuple1, _), Patterns.TupleGet(tuple2, _)) -> deconstructExprEqual tuple1 tuple2
        | (Patterns.PropertyGet(Some term1, _, []), Patterns.PropertyGet(Some term2, _, [])) ->
            deconstructExprEqual term1 term2
        | (ExprShape.ShapeVar(v1), ExprShape.ShapeVar(v2)) -> v1 = v2
        | _ -> false

    let getPropertyInfo (termExpr: Expr) (propertyInfo: System.Reflection.PropertyInfo) =
        if (FSharpType.IsUnion termExpr.Type) then
            let cases = FSharpType.GetUnionCases termExpr.Type

            let case =
                Seq.ofArray cases
                |> Seq.filter (fun c ->
                    c.GetFields() |> Seq.ofArray |> Seq.exists (fun f -> f.Name = propertyInfo.Name))
                |> Seq.exactlyOne

            let fields = case.GetFields()

            let index = fields |> Array.findIndex (fun p -> p.Name = propertyInfo.Name)

            let argTypes = fields |> Array.map (fun f -> f.PropertyType)

            (UnionCase(case), argTypes, index)
        else if (FSharpType.IsRecord termExpr.Type) then
            let fields = FSharpType.GetRecordFields(termExpr.Type)

            let index = fields |> Array.findIndex (fun p -> p.Name = propertyInfo.Name)

            let argTypes = fields |> Array.map (fun f -> f.PropertyType)

            (Record(termExpr.Type), argTypes, index)
        else
            raise (System.Exception($"type not supported in deconstruct {termExpr.Type.Name}"))

    let rec expandPropertyGet expr deconstructVars =
        let (termExpr, ctor, propertyIndex, argTypes) =
            match expr with
            | Patterns.TupleGet(tupleExpr, tupleIndex) ->
                (tupleExpr, tupleConstructor tupleExpr.Type, tupleIndex, FSharpType.GetTupleElements tupleExpr.Type)
            | Patterns.PropertyGet(Some termExpr, propertyInfo, []) ->
                let (ctor, argTypes, propertyIndex) = getPropertyInfo termExpr propertyInfo
                (termExpr, ctor, propertyIndex, argTypes)
            | _ -> raise (System.Exception($"expression not supported in deconstruct {expr}"))

        let deconstructVars' =
            match termExpr with
            | ExprShape.ShapeVar _ -> deconstructVars
            | _ -> expandPropertyGet termExpr deconstructVars |> snd

        let argVars =
            seq { 0 .. (Array.length (argTypes) - 1) }
            |> Seq.map (fun i -> None)
            |> Array.ofSeq

        Array.set argVars propertyIndex (Some(expr, None))
        let result = (termExpr, ctor, argVars, argTypes)
        (result, result :: deconstructVars')

    let collectDeconstructPropertyVars var expr termExpr index deconstructVars : DeconstructVars =
        match (List.tryFind (fun (e, _, _, _) -> deconstructExprEqual e termExpr) deconstructVars) with
        | Some(_, _, unifyArgs: DeconstructUnifyArg array, _) ->
            match unifyArgs.[index] with
            | Some(_, Some _) -> raise (System.Exception("expression deconstructed twice"))
            | _ ->
                Array.set unifyArgs index (Some(expr, Some var))
                deconstructVars
        | None ->
            let ((_, _, argVars, _), deconstructVars') as newVar =
                expandPropertyGet expr deconstructVars

            Array.set argVars index (Some(expr, Some var))
            deconstructVars'

    let collectDeconstructVars deconstructVars (var, expr) : DeconstructVars =
        match expr with
        | Patterns.TupleGet(tupleExpr, index) -> collectDeconstructPropertyVars var expr tupleExpr index deconstructVars
        | Patterns.PropertyGet(Some termExpr, propertyInfo, []) ->
            let (_, _, index) = getPropertyInfo termExpr propertyInfo
            collectDeconstructPropertyVars var expr termExpr index deconstructVars
        | _ -> deconstructVars

    let rec translateSubExpr expr =
        parse {
            do! updateSourceInfo expr
            let! sourceInfo = currentSourceInfo

            match expr with
            | DerivedPatterns.SpecificCall (<@@ casgliad.exists @@>) (_, _, [ ExprShape.ShapeLambda(v, expr); _; _ ]) ->
                // translateArgs will strip off any TupleGet calls to deconstruct the
                // tuple of existentially quantified variables. We're only using the lambda
                // to introduce new variables, we don't care what was passed in.
                let! (_, goal) = translateArgs v expr []
                return goal.Goal
            | DerivedPatterns.SpecificCall (<@@ casgliad.call @@>) (_,
                                                                    _,
                                                                    [ Patterns.PropertyGet(Some calleeObj, callee, [])
                                                                      Patterns.NewTuple(args)
                                                                      _
                                                                      _ ]) ->
                return! translateCall calleeObj callee args
            | DerivedPatterns.SpecificCall (<@@ (=) @@>) (_, [ unifyType ], [ lhs; rhs ]) ->
                return! translateUnify lhs rhs unifyType (initUnifyContext ExplicitUnify)
            | Patterns.Call(None, callee, args) ->
                let! (argVars, extraGoals) =
                    translateCallArgs false args (fun index ->
                        initUnifyContext (CallArgUnify(FSharpCallee(callee), index)))

                let goal = FSharpCall((callee, invalidProcId), None, argVars)

                return
                    List.append extraGoals [ initGoal sourceInfo goal ]
                    |> Simplify.flattenConjunction
            | UnionMatch(ExprShape.ShapeVar v, cases, canFail) ->
                let! caseGoals = translateMatchExpr v cases
                return Disjunction(caseGoals)
            | DerivedPatterns.AndAlso(condExpr, thenExpr) ->
                let! condGoal = translateSubExprGoal condExpr
                let! thenGoal = translateSubExprGoal thenExpr

                return Simplify.flattenConjunction [ condGoal; thenGoal ]
            | DerivedPatterns.OrElse(condExpr, elseExpr) ->
                let! condGoal = translateSubExprGoal condExpr
                let! elseGoal = translateSubExprGoal elseExpr

                return Simplify.flattenDisjunction [ condGoal; elseGoal ]
            | Deconstruct(deconstructExprs, subExpr) ->
                let! deconstructGoals = translateDeconstructExprs deconstructExprs
                let! subGoal = translateSubExprGoal subExpr

                return List.append deconstructGoals [ subGoal ] |> Simplify.flattenConjunction
            | Patterns.Let(v, binding, expr) ->
                // Introduces a fresh variable and unifies it immediately.
                let! unifyGoalExpr = translateUnify (Expr.Var v) binding v.Type (initUnifyContext ExplicitUnify)
                let! exprGoal = translateSubExprGoal expr

                return Simplify.flattenConjunction [ initGoal sourceInfo unifyGoalExpr; exprGoal ]
            | True' _ -> return Conjunction([])
            | False' _ -> return Disjunction([])
            | ExprShape.ShapeVar v ->
                if (v.Type = typeof<bool>) then
                    let! lhsVar = newQVar v

                    let rhs = makeCtorRhs (Constant(BoolValue(true), typeof<bool>)) []

                    return initUnify lhsVar rhs (initUnifyContext ExplicitUnify)
                else
                    return! unsupportedExpression expr
            | ExprShape.ShapeLambda(v, subExpr) -> return! unsupportedExpression expr
            | ExprShape.ShapeCombination(combo, exprs) -> return! unsupportedExpression expr
        }

    and translateSubExprGoal expr =
        parse {
            let! sourceInfo = currentSourceInfo
            let! goal = translateSubExpr expr
            return initGoal sourceInfo goal
        }

    and translateMatchCase var (case, expr) goals =
        parse {
            let! sourceInfo = currentSourceInfo

            let fieldTypes =
                match case with
                | UnionCase(unionCase) -> unionCase.GetFields() |> Array.map (fun f -> f.PropertyType)
                | _ -> [||]

            let! fieldVars = newVars (List.ofArray fieldTypes)
            // TODO fix unify context
            let unifyGoal =
                initUnify var (makeCtorRhs case fieldVars) (initUnifyContext ImplicitUnify)

            let! goal = translateSubExprGoal expr

            let disjunct =
                initGoal sourceInfo (Simplify.flattenConjunction [ initGoal sourceInfo unifyGoal; goal ])

            return disjunct :: goals
        }

    and translateMatchExpr var cases =
        parse {
            let! v = newQVar var
            let! goals = foldWithState2 (translateMatchCase v) [] cases
            return List.rev goals
        }

    and translateDeconstructExprs (deconstructExprs: (Var * Expr) list) =
        parse {
            let deconstructVars = List.fold collectDeconstructVars [] deconstructExprs

            return! translateDeconstructVars deconstructVars
        }

    and translateDeconstructVars (deconstructVars: DeconstructVars) =
        parse {
            let rec assignUnifyArgs
                (unifyArgTypes: System.Type array)
                (unifyArgs: DeconstructUnifyArg array)
                (assignedVars: AssignedDeconstructVar list)
                i
                =
                parse {
                    if (i >= unifyArgTypes.Length) then
                        return []
                    else
                        let! unifyArgsVars = assignUnifyArgs unifyArgTypes unifyArgs assignedVars (i + 1)

                        match unifyArgs.[i] with
                        | Some(_, Some v) ->
                            let! argVar = newQVar v
                            return argVar :: unifyArgsVars
                        | Some(expr, None) ->
                            match (List.tryFind (fun (_, e, _, _) -> deconstructExprMatch e expr) assignedVars) with
                            | Some(argVar, _, _, _) -> return argVar :: unifyArgsVars
                            | None -> return raise (System.Exception($"unassigned expression {expr}"))
                        | None ->
                            let! v = newVar unifyArgTypes.[i]
                            return v :: unifyArgsVars
                }

            let assignVar
                (expr: Expr, ctor: Constructor, unifyArgs, unifyArgTypes)
                (assignedVars: AssignedDeconstructVar list)
                =
                parse {
                    let! assignedVar =
                        match (List.tryFind (fun (_, e, _, _) -> deconstructExprMatch e expr) assignedVars) with
                        | Some(v, _, _, _) -> parse { return v }
                        | None ->
                            match expr with
                            | ExprShape.ShapeVar v -> newQVar v
                            | _ -> newVar expr.Type

                    let! unifyArgs' = assignUnifyArgs unifyArgTypes unifyArgs assignedVars 0

                    return ((assignedVar, expr, ctor, unifyArgs') :: assignedVars)
                }

            let! assignedDeconstructVars = foldWithState2 assignVar [] deconstructVars

            let generateDeconstructGoal sourceInfo (var, _, ctor, unifyArgs) =
                let unifyRhs = makeCtorRhs ctor unifyArgs
                // TODO: fix context
                let unifyContext = initUnifyContext ImplicitUnify
                initGoal sourceInfo (initUnify var unifyRhs unifyContext)

            let! sourceInfo = currentSourceInfo
            return List.map (generateDeconstructGoal sourceInfo) assignedDeconstructVars
        }

    and translateArgs argVar expr args =
        parse {
            do! updateSourceInfo expr

            match expr with
            | Patterns.Let(arg, Patterns.TupleGet(ExprShape.ShapeVar argVar1, _), subExpr) when argVar = argVar1 ->
                // Found extraction of argument from tuple of arguments.
                let! relationArgVar = newQVar arg
                return! translateArgs argVar subExpr (relationArgVar :: args)
            | _ ->
                let! goal = translateSubExprGoal expr
                return (List.rev args, goal)
        }

    let translateExpr expr =
        parse {
            do! updateSourceInfo expr

            match expr with
            | Patterns.Lambda(argVar, subExpr) ->
                match subExpr with
                | Patterns.Let(_, Patterns.TupleGet(ExprShape.ShapeVar argVar1, _), _) when
                    argVar.Name = "tupledArg" && argVar = argVar1
                    ->
                    return! translateArgs argVar subExpr []
                | _ ->
                    let! relationArgVar = newQVar argVar
                    let! goal = translateSubExprGoal subExpr
                    return ([ relationArgVar ], goal)
            | _ ->
                let! sourceInfo = currentSourceInfo
                let! goalExpr = unsupportedExpression expr
                return ([], initGoal sourceInfo goalExpr)
        }
