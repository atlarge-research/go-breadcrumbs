package dataflow

import (
	"cmd/compile/internal/ir"
	"cmd/compile/internal/types"
	"log"
)

func Funcs(all []ir.Node) {
	for _, n := range all {
		if n.Op() == ir.ODCLFUNC {
			n := n.(*ir.Func)
			if n.Pragma&ir.Dataflow != 0 {
				log.Println("Phew!")
				instrument(n)
			}
		}
	}
}

func instrument(fn *ir.Func) {
	intType := types.Types[types.TINT]

	ft := fn.Type().FuncType()
	// The results type needs to be a struct according to newsignature in types/.type.go
	prevParamsFields := ft.Params.FieldSlice()
	prevParamsSize := len(prevParamsFields)
	newParamsFields := make([]*types.Field, 2*prevParamsSize)
	for i := 0; i < prevParamsSize; i++ {
		prevField := prevParamsFields[i]
		newParamsFields[i] = prevField

		prevSym := prevField.Sym
		newSym := &types.Sym{
			Name: "_df_" + prevSym.Name,
			Pkg:  prevSym.Pkg,
		}
		newName := ir.NewDeclNameAt(prevField.Pos, ir.ONAME, newSym)
		newName.Class = ir.PPARAM
		newName.Curfn = prevField.Nname.(*ir.Name).Curfn
		newName.SetType(intType)

		// paramNameToDfNameMap[prevSym.Name] = newName
		newField := types.NewField(prevField.Pos, newSym, intType)
		newField.Nname = newName

		newParamsFields[i+prevParamsSize] = newField
	}
	newParamsStruct := types.NewStruct(types.NoPkg, newParamsFields)
	newParamsStruct.StructType().Funarg = ft.Params.StructType().Funarg
	ft.Params = newParamsStruct

	// The results type needs to be a struct according to newsignature in types/.type.go
	prevResultsFields := ft.Results.FieldSlice()
	prevResultsSize := len(prevResultsFields)
	newResultsFields := make([]*types.Field, 2*prevResultsSize)
	for i := 0; i < prevResultsSize; i++ {
		prevResField := prevResultsFields[i]
		newResultsFields[i] = prevResField

		prevSym := prevResField.Sym
		newSym := &types.Sym{
			Name: "_df_" + prevSym.Name,
			Pkg:  prevSym.Pkg,
		}
		newName := ir.NewDeclNameAt(prevResField.Pos, ir.ONAME, newSym)
		newName.Class = ir.PPARAM
		newName.Curfn = prevResField.Nname.(*ir.Name).Curfn
		newName.SetType(intType)

		newField := types.NewField(prevResField.Pos, newSym, intType)
		newField.Nname = newName

		newResultsFields[i+prevResultsSize] = newField
	}
	newResultsStruct := types.NewStruct(types.NoPkg, newResultsFields)
	newResultsStruct.StructType().Funarg = ft.Results.StructType().Funarg
	ft.Results = newResultsStruct
}
