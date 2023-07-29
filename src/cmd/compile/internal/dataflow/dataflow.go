package dataflow

import (
	"bufio"
	"cmd/compile/internal/ir"
	"cmd/compile/internal/typecheck"
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"log"
	"os"
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
	dfBmType := types.Types[types.TINT64]

	ft := fn.Type().FuncType()
	// The results type needs to be a struct according to newsignature in types/.type.go
	prevParamsFields := ft.Params.FieldSlice()
	prevParamsSize := len(prevParamsFields)
	newParamsFields := make([]*types.Field, 2*prevParamsSize)
	paramsDf := make([]*ir.Name, prevParamsSize)
	for i := 0; i < prevParamsSize; i++ {
		prevField := prevParamsFields[i]
		newParamsFields[i] = prevField

		prevSym := prevField.Sym
		newSym := &types.Sym{
			Name: "_df_" + prevSym.Name,
			Pkg:  prevSym.Pkg,
		}
		newName := ir.NewNameAt(prevField.Pos, newSym)
		newName.Class = ir.PPARAM
		newName.Curfn = prevField.Nname.(*ir.Name).Curfn
		newName.SetType(dfBmType)

		newField := types.NewField(prevField.Pos, newSym, dfBmType)
		newField.Nname = newName

		newParamsFields[i+prevParamsSize] = newField
		paramsDf[i] = newName
	}
	newParamsStruct := types.NewStruct(types.NoPkg, newParamsFields)
	newParamsStruct.StructType().Funarg = ft.Params.StructType().Funarg
	ft.Params = newParamsStruct

	// The results type needs to be a struct according to newsignature in types/.type.go
	prevResultsFields := ft.Results.FieldSlice()
	prevResultsSize := len(prevResultsFields)
	newResultsFields := make([]*types.Field, 2*prevResultsSize)
	resultsDf := make([]ir.Node, prevResultsSize)
	for i := 0; i < prevResultsSize; i++ {
		prevResField := prevResultsFields[i]
		newResultsFields[i] = prevResField

		prevSym := prevResField.Sym
		newSym := &types.Sym{
			Name: "_df_" + prevSym.Name,
			Pkg:  prevSym.Pkg,
		}
		newName := ir.NewNameAt(prevResField.Pos, newSym)
		newName.Class = ir.PPARAM
		newName.Curfn = prevResField.Nname.(*ir.Name).Curfn
		newName.SetType(dfBmType)

		newField := types.NewField(prevResField.Pos, newSym, dfBmType)
		newField.Nname = newName

		newResultsFields[i+prevResultsSize] = newField
		resultsDf[i] = newName
	}
	newResultsStruct := types.NewStruct(types.NoPkg, newResultsFields)
	newResultsStruct.StructType().Funarg = ft.Results.StructType().Funarg
	ft.Results = newResultsStruct

	// Receive params dataflow from caller
	fn.Dcl = append(fn.Dcl, paramsDf...)

	if fn.Nname.Sym().Name == "boom" {
		file, _ := os.Create("boom_ast.dump")
		defer file.Close()
		w := bufio.NewWriter(file)
		ir.FDumpList(w, "cool", fn.Body)
		w.Flush()
	}

	for _, n := range fn.Body {
		if n.Op() == ir.ORETURN {
			n := n.(*ir.ReturnStmt)

			// Send back dataflow of return values to caller
			n.Results = append(n.Results, resultsDf...)
		}
	}

	totalNodes := 0
	for _, n := range fn.Body {
		totalNodes += 1
		ir.DoChildren(n, func(_ ir.Node) bool {
			totalNodes += 1
			return false
		})
	}

	dfArrayType := types.NewArray(dfBmType, int64(totalNodes*3))
	types.CalcSize(dfArrayType)

	dfArrSym := &types.Sym{
		Name: "__dataflow_arr",
		Pkg:  fn.Sym().Pkg,
	}
	dfArrName := ir.NewNameAt(src.NoXPos, dfArrSym)
	dfArrName.Class = ir.PAUTO
	dfArrName.Curfn = fn
	dfArrName.SetType(dfArrayType)
	dfArrName.SetUsed(true)

	blockArrayType := types.NewArray(dfBmType, int64(totalNodes))
	types.CalcSize(blockArrayType)

	blockDfSym := &types.Sym{
		Name: "__blockdf_arr",
		Pkg:  fn.Sym().Pkg,
	}
	blockDfName := ir.NewNameAt(src.NoXPos, blockDfSym)
	blockDfName.Class = ir.PAUTO
	blockDfName.Curfn = fn
	blockDfName.SetType(blockArrayType)
	blockDfName.SetUsed(true)

	fn.Dcl = append(fn.Dcl, dfArrName)
	fn.Dcl = append(fn.Dcl, blockDfName)

	as1 := typecheck.Stmt(ir.NewAssignStmt(src.NoXPos, dfArrName, nil))
	as2 := typecheck.Stmt(ir.NewAssignStmt(src.NoXPos, blockDfName, nil))
	fn.Body.Prepend(as1, as2)
}
