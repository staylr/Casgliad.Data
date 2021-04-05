namespace Kanren.Data.Compiler

type VarSet =
    private {
        NextVar : int;
        Vars : Map<int, Quotations.Var>;
        QVars: Set<Quotations.Var>
    }
    with
        static member init = { NextVar = 0; Vars = Map.empty; QVars = Set.empty }

        member v.addQuotationVar(var) =
            if (v.QVars.Contains(var)) then v else v.addVar(var)

        member v.addVar(var) =
            { NextVar = v.NextVar + 1; Vars = v.Vars.Add(v.NextVar, var); QVars = v.QVars.Add(var) }

        member v.newNamedVar(name, varType) =
            let var = Quotations.Var(name, varType)
            (v.addVar(var), var)

        member v.newVar(varType) =
            let nextVar = v.NextVar
            let name = "kdc__" + nextVar.ToString()
            v.newNamedVar(name, varType)
