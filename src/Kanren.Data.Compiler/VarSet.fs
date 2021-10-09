namespace Kanren.Data.Compiler

[<Measure>]
type varIdMeasure

type VarId = int<varIdMeasure>


type SetOfVar = TagSet<varIdMeasure>

type ProgVar =
    { Id: VarId
      Name: string
      VarType: System.Type }

type VarSet =
    private
        { NextVar: VarId
          Vars: Map<VarId, ProgVar>
          VarNames: Map<string, ProgVar>
          QVars: Map<Quotations.Var, ProgVar> }
    static member init =
        { NextVar = 0<varIdMeasure>
          Vars = Map.empty
          VarNames = Map.empty
          QVars = Map.empty }

    member v.newNamedVar(varName: string, varType: System.Type) : (VarSet * ProgVar) =
        let varId = v.NextVar

        let rec makeUniqueName name =
            if (v.VarNames.ContainsKey(name)) then
                makeUniqueName $"{name}__{varId}"
            else
                name

        let progVar =
            { Id = v.NextVar
              Name = makeUniqueName varName
              VarType = varType }

        ({ NextVar = v.NextVar + 1<varIdMeasure>
           Vars = v.Vars.Add(varId, progVar)
           VarNames = v.VarNames.Add(progVar.Name, progVar)
           QVars = v.QVars },
         progVar)

    member v.addQuotationVar(qvar) =
        if (v.QVars.ContainsKey(qvar)) then
            (v, v.QVars.[qvar])
        else
            let (v', var) = v.newNamedVar (qvar.Name, qvar.Type)

            ({ v' with
                   QVars = v'.QVars.Add(qvar, var) },
             var)

    member v.newVar(varType) =
        let nextVar = v.NextVar
        let name = "kdc__" + nextVar.ToString()
        v.newNamedVar (name, varType)

    member this.Item
        with get (index: VarId) = this.Vars.[index]
