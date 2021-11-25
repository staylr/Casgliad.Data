namespace Kanren.Data.Compiler

[<Measure>]
type internal varIdMeasure

type internal VarId = int<varIdMeasure>


type internal SetOfVar = TagSet<varIdMeasure>

type internal ProgVar =
    { Id: VarId
      Name: string
      VarType: System.Type }

type internal VarSet =
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
            if (v.VarNames.ContainsKey (name)) then
                makeUniqueName $"{name}__{varId}"
            else
                name

        let progVar =
            { Id = v.NextVar
              Name = makeUniqueName varName
              VarType = varType }

        ({ NextVar = v.NextVar + 1<varIdMeasure>
           Vars = v.Vars.Add (varId, progVar)
           VarNames = v.VarNames.Add (progVar.Name, progVar)
           QVars = v.QVars },
         progVar)

    member v.addQuotationVar(quotationVar) =
        if (v.QVars.ContainsKey (quotationVar)) then
            (v, v.QVars.[quotationVar])
        else
            let (v', var) =
                v.newNamedVar (quotationVar.Name, quotationVar.Type)

            ({ v' with
                   QVars = v'.QVars.Add (quotationVar, var) },
             var)

    member v.newVar(varType) =
        let nextVar = v.NextVar
        let name = "kdc__" + nextVar.ToString ()
        v.newNamedVar (name, varType)

    member this.Item
        with get (index: VarId) = this.Vars.[index]
