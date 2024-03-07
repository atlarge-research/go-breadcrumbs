package dataflow

import (
	"cmd/compile/internal/ir"
	"cmd/compile/internal/typecheck"
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"log"
	"strings"
)

func Funcs(all []ir.Node) {
	for _, n := range all {
		if n.Op() == ir.ODCLFUNC {
			n := n.(*ir.Func)
			if n.Pragma&ir.Dataflow != 0 {
				log.Println("Phew!")
				instrument(n)
			} else {
				// log.Println("Not df " + n.Nname.Sym().Name)
			}
		}
	}
}

func instrument(fn *ir.Func) {
	dfBmType := types.Types[types.TINT64]

	ft := fn.Type().FuncType()
	// The parameters type needs to be a struct according to newsignature in types/.type.go
	prevParamsFields := ft.Params.FieldSlice()
	prevParamsSize := len(prevParamsFields)
	newParamsFields := make([]*types.Field, 0, 2*prevParamsSize)
	paramsDf := make([]*ir.Name, 0, 2*prevParamsSize)
	paramsDfPtrs := make([]*ir.Name, 0, prevParamsSize)
	// Param order is values..., (df, [dfptr])..., blockdf
	for i := 0; i < prevParamsSize; i++ {
		prevField := prevParamsFields[i]

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

		newParamsFields = append(newParamsFields, newField)
		paramsDf = append(paramsDf, newName)

		if prevField.Type.IsPtr() {
			newSym := &types.Sym{
				Name: "_dfptr_" + prevSym.Name,
				Pkg:  prevSym.Pkg,
			}
			newName := ir.NewNameAt(prevField.Pos, newSym)
			newName.Class = ir.PPARAM
			newName.Curfn = prevField.Nname.(*ir.Name).Curfn
			newName.SetType(dfBmType.PtrTo())

			newField := types.NewField(prevField.Pos, newSym, dfBmType.PtrTo())
			newField.Nname = newName

			newParamsFields = append(newParamsFields, newField)
			paramsDf = append(paramsDf, newName)
			paramsDfPtrs = append(paramsDfPtrs, newName)
		}
	}
	// Pass block df as the last df parameter
	newSym := &types.Sym{
		Name: "_dfblock_",
		Pkg:  fn.Sym().Pkg,
	}
	newName := ir.NewNameAt(fn.Pos(), newSym)
	newName.Class = ir.PPARAM
	newName.Curfn = fn
	newName.SetType(dfBmType)

	newField := types.NewField(fn.Pos(), newSym, dfBmType)
	newField.Nname = newName

	newParamsFields = append(newParamsFields, newField)
	paramsDf = append(paramsDf, newName)

	allParamsFields := append(prevParamsFields, newParamsFields...)
	newParamsStruct := types.NewStruct(types.NoPkg, allParamsFields)
	newParamsStruct.StructType().Funarg = ft.Params.StructType().Funarg
	ft.Params = newParamsStruct

	// The results type needs to be a struct according to newsignature in types/.type.go
	prevResultsFields := ft.Results.FieldSlice()
	prevResultsSize := len(prevResultsFields)
	newResultsFields := make([]*types.Field, 0, 2*prevResultsSize)
	resultsDf := make([]*ir.Name, 0, 2*prevResultsSize)
	resultsDfNode := make([]ir.Node, 0, 2*prevResultsSize)
	// Return order is Param order is values..., (df, dfptr)..., blockdf
	// Notice that dfptrs are not optional in returns, unlike in input parameters
	for i := 0; i < prevResultsSize; i++ {
		prevResField := prevResultsFields[i]

		prevSym := prevResField.Sym
		newSym := &types.Sym{
			Name: "_df_" + prevSym.Name,
			Pkg:  prevSym.Pkg,
		}
		newName := ir.NewNameAt(prevResField.Pos, newSym)
		newName.Class = ir.PPARAMOUT
		newName.Curfn = prevResField.Nname.(*ir.Name).Curfn
		newName.SetType(dfBmType)

		newField := types.NewField(prevResField.Pos, newSym, dfBmType)
		newField.Nname = newName

		newResultsFields = append(newResultsFields, newField)
		resultsDf = append(resultsDf, newName)
		resultsDfNode = append(resultsDfNode, newName)

		// Df ptrs are returned by default. They will be null for non ptr values
		newSym = &types.Sym{
			Name: "_dfptr_" + prevSym.Name,
			Pkg:  prevSym.Pkg,
		}
		newName = ir.NewNameAt(prevResField.Pos, newSym)
		newName.Class = ir.PPARAMOUT
		newName.Curfn = prevResField.Nname.(*ir.Name).Curfn
		newName.SetType(dfBmType.PtrTo())

		newField = types.NewField(prevResField.Pos, newSym, dfBmType.PtrTo())
		newField.Nname = newName

		newResultsFields = append(newResultsFields, newField)
		resultsDf = append(resultsDf, newName)
		resultsDfNode = append(resultsDfNode, newName)
	}
	// Return block df as the last df parameter
	newSym = &types.Sym{
		Name: "_dfblockret_",
		Pkg:  fn.Sym().Pkg,
	}
	newName = ir.NewNameAt(fn.Pos(), newSym)
	newName.Class = ir.PPARAMOUT
	newName.Curfn = fn
	newName.SetType(dfBmType)

	newField = types.NewField(fn.Pos(), newSym, dfBmType)
	newField.Nname = newName

	newResultsFields = append(newResultsFields, newField)
	resultsDf = append(resultsDf, newName)
	resultsDfNode = append(resultsDfNode, newName)

	allResultsFields := append(prevResultsFields, newResultsFields...)
	newResultsStruct := types.NewStruct(types.NoPkg, allResultsFields)
	newResultsStruct.StructType().Funarg = ft.Results.StructType().Funarg
	ft.Results = newResultsStruct

	// Receive params dataflow from caller
	fn.Dcl = append(fn.Dcl, paramsDf...)
	fn.Dcl = append(fn.Dcl, resultsDf...)

	// if fn.Nname.Sym().Name == "boom" {
	// 	file, _ := os.Create("boom_ast.dump")
	// 	defer file.Close()
	// 	w := bufio.NewWriter(file)
	// 	ir.FDumpList(w, "cool", fn.Body)
	// 	w.Flush()
	// }

	for _, n := range fn.Body {
		if n.Op() == ir.ORETURN {
			n := n.(*ir.ReturnStmt)

			// Send back dataflow of return values to caller
			n.Results = append(n.Results, resultsDfNode...)
		}
	}

	dfInHeap := false
	blockDfInHeap := false
	totalNodes := 0
	decisionNodes := 0
	for _, n := range fn.Body {
		totalNodes += 1
		ir.DoChildren(n, func(current ir.Node) bool {
			if current.Op() == ir.OCALLFUNC {
				current := current.(*ir.CallExpr)
				fnname := current.X.Sym().Name
				if strings.HasPrefix(fnname, "DfGetArr") {
					dfInHeap = true
				}
				if strings.HasPrefix(fnname, "DfGetBlockArr") {
					blockDfInHeap = true
				}
			}

			cOp := current.Op()
			if cOp == ir.OIF || cOp == ir.OFOR || cOp == ir.OSWITCH ||
				cOp == ir.OJUMPTABLE {
				decisionNodes += 1
			}

			totalNodes += 1
			return false
		})
	}

	// Initializing dataflow arrays
	dfArrSizeBase := totalNodes // +
	// (decisionNodes * 10) // dfptr related ifs are also included
	// multipliers based on addr,load,addr,load,or,addr,store
	// if ptr add ptr,load,ptr,load,or,ptr,store
	dfArrayType := types.NewArray(dfBmType, int64(dfArrSizeBase*14))
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

	blockArrayType := types.NewArray(dfBmType, int64(dfArrSizeBase))
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

	dfArrDecl := typecheck.Stmt(ir.NewDecl(src.NoXPos, ir.ODCL, dfArrName))
	dfArrAssign := typecheck.Stmt(ir.NewAssignStmt(src.NoXPos, dfArrName, nil))
	blockDfDecl := typecheck.Stmt(ir.NewDecl(src.NoXPos, ir.ODCL, blockDfName))
	blockDfAssign := typecheck.Stmt(ir.NewAssignStmt(src.NoXPos, blockDfName, nil))
	fn.Body.Prepend(dfArrDecl, dfArrAssign, blockDfDecl, blockDfAssign)

	if dfInHeap {
		dfArrRetSym := &types.Sym{
			Name: "__dfarrret_arr",
			Pkg:  fn.Sym().Pkg,
		}
		dfArrRetName := ir.NewNameAt(src.NoXPos, dfArrRetSym)
		dfArrRetName.Class = ir.PAUTO
		dfArrRetName.Curfn = fn
		dfArrRetName.SetType(dfArrayType)
		dfArrRetName.SetUsed(true)
		dfArrRetName.SetAddrtaken(true)
		dfArrRetName.SetEsc(ir.EscHeap)

		fn.Dcl = append(fn.Dcl, dfArrRetName)
		dfArrRetDecl := typecheck.Stmt(ir.NewDecl(src.NoXPos, ir.ODCL, dfArrRetName))
		dfArrRetAssign := typecheck.Stmt(ir.NewAssignStmt(src.NoXPos, dfArrRetName, nil))
		dfArrRetDecl.SetEsc(ir.EscHeap)
		dfArrRetAssign.SetEsc(ir.EscHeap)

		fn.Body.Prepend(dfArrRetDecl, dfArrRetAssign)
	}

	if blockDfInHeap {
		dfArrRetSym := &types.Sym{
			Name: "__blockdfarrret_arr",
			Pkg:  fn.Sym().Pkg,
		}
		dfArrRetName := ir.NewNameAt(src.NoXPos, dfArrRetSym)
		dfArrRetName.Class = ir.PAUTO
		dfArrRetName.Curfn = fn
		dfArrRetName.SetType(dfArrayType)
		dfArrRetName.SetUsed(true)
		dfArrRetName.SetAddrtaken(true)
		dfArrRetName.SetEsc(ir.EscHeap)

		fn.Dcl = append(fn.Dcl, dfArrRetName)
		dfArrRetDecl := typecheck.Stmt(ir.NewDecl(src.NoXPos, ir.ODCL, dfArrRetName))
		dfArrRetAssign := typecheck.Stmt(ir.NewAssignStmt(src.NoXPos, dfArrRetName, nil))
		dfArrRetDecl.SetEsc(ir.EscHeap)
		dfArrRetAssign.SetEsc(ir.EscHeap)

		fn.Body.Prepend(dfArrRetDecl, dfArrRetAssign)
	}
}
