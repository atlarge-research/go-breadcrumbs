package ssa

import (
	"cmd/compile/internal/ir"
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"log"
)

func dataflowInstrument(f *Func) {
	if f.Dataflow {
		types.CalcSizeDisabled = false

		log.Println("Cool!")
		firstBlock := f.Blocks[0]
		mem := firstBlock.Values[0]
		sp := firstBlock.Values[1]
		initialValues := firstBlock.Values[:]

		lastValId := initialValues[len(initialValues)-1].ID

		// Create array to hold the dataflow values
		intType := types.Types[types.TINT]
		int32Type := types.Types[types.TINT32]
		arrayType := types.NewArray(intType, int64(lastValId))
		types.CalcSize(arrayType)

		arr1 := firstBlock.NewValue2(src.NoXPos, OpLocalAddr,
			types.NewPtr(arrayType), sp, mem)
		zero1 := firstBlock.NewValue2I(src.NoXPos, OpZero, types.TypeMem, arrayType.Size(), arr1, mem)
		zero1.Aux = arrayType

		lastMem := zero1
		// lastMemReturnIdx := int64(0)

		paramNameToDfNameMap := make(map[string]*ir.Name)

		types.CalcSizeDisabled = true

		// Walk through the value and propagate dataflow based on their parameters
		for vi := 0; vi < len(initialValues); vi++ {
			currentVal := initialValues[vi]
			valuePos := currentVal.Pos

			if currentVal.Op == OpArg {
				prevName := currentVal.Aux.(*ir.Name)
				prevSym := prevName.Sym()
				newName := paramNameToDfNameMap[prevSym.Name]

				// newName := ir.NewDeclNameAt(valuePos, ir.ONAME, newSym)
				// newName.Class = ir.PPARAM
				// newName.Curfn = prevName.Curfn
				// newName.SetType(intType)

				argDf := firstBlock.NewValue0A(valuePos, OpArg, intType, newName)

				dfArr := firstBlock.NewValue2(valuePos, OpLocalAddr,
					types.NewPtr(arrayType), sp, lastMem)
				argDfPtr := firstBlock.NewValue2(valuePos, OpPtrIndex, arrayType,
					dfArr, f.ConstInt32(int32Type, int32(currentVal.ID)))
				lastMem = firstBlock.NewValue3A(valuePos, OpStore, types.TypeMem, intType,
					argDfPtr, argDf, lastMem)

				continue
			}

			// This like memory init, sp init, args dont need to be tracked
			if len(currentVal.Args) < 1 {
				continue
			}

			if currentVal.Op == OpMakeResult {
				numPrevRealArgs := len(currentVal.Args) - 1
				// len-1 because last arg is memory location
				resDf := make([]*Value, numPrevRealArgs)
				for argidx := 0; argidx < numPrevRealArgs; argidx++ {
					arg1 := currentVal.Args[argidx]
					dfArr := firstBlock.NewValue2(valuePos, OpLocalAddr,
						types.NewPtr(arrayType), sp, lastMem)
					argDfPtr := firstBlock.NewValue2(valuePos, OpPtrIndex, arrayType,
						dfArr, f.ConstInt32(int32Type, int32(arg1.ID)))
					resDf[argidx] = firstBlock.NewValue2(valuePos, OpLoad, intType, argDfPtr, lastMem)
				}

				prevRealArgs := currentVal.Args[:numPrevRealArgs]
				currentVal.resetArgs()
				currentVal.AddArgs(prevRealArgs...)
				currentVal.AddArgs(resDf...)
				currentVal.AddArgs(lastMem)
				// Take care to pass the mem parameter from new zero/alloc instructions
				// NOT the old one

				prevType := currentVal.Type

				// New results order, values, dfs of values, memory
				newResultsSize := 2*(numPrevRealArgs) + 1
				tys := make([]*types.Type, newResultsSize, newResultsSize)
				for i := 0; i < numPrevRealArgs; i++ {
					tys[i] = prevType.FieldType(i)
				}
				for i := numPrevRealArgs; i < 2*numPrevRealArgs; i++ {
					tys[i] = intType
				}
				tys[len(tys)-1] = types.TypeMem
				newResultsTypes := types.NewResults(tys)
				currentVal.Type = newResultsTypes

				continue
			}

			if currentVal.Op == OpStaticLECall {
				// No need to change type for this.
				// Type was obtained automatically after
				// func signature modification

				numPrevRealArgs := int64(len(currentVal.Args) - 1)
				// len-1 because last arg is memory location
				resDf := make([]*Value, numPrevRealArgs)
				for argidx := int64(0); argidx < numPrevRealArgs; argidx++ {
					arg1 := currentVal.Args[argidx]
					dfArr := firstBlock.NewValue2(valuePos, OpLocalAddr,
						types.NewPtr(arrayType), sp, lastMem)
					argDfPtr := firstBlock.NewValue2(valuePos, OpPtrIndex, arrayType,
						dfArr, f.ConstInt32(int32Type, int32(arg1.ID)))
					resDf[argidx] = firstBlock.NewValue2(valuePos, OpLoad, intType, argDfPtr, lastMem)
				}

				prevRealArgs := currentVal.Args[:numPrevRealArgs]
				currentVal.resetArgs()
				currentVal.AddArgs(prevRealArgs...)
				currentVal.AddArgs(resDf...)
				currentVal.AddArgs(lastMem)

				lastMem = currentVal

				// Need to add additional selectNs for dataflow returns
				for dfidx := numPrevRealArgs; dfidx < 2*numPrevRealArgs; dfidx++ {
					firstBlock.NewValue1I(valuePos, OpSelectN, intType, dfidx, currentVal)
				}

				// lastMemReturnIdx = 2 * numPrevRealArgs

				continue
			}

			if currentVal.Op == OpSelectN &&
				currentVal.Type == types.TypeMem {

				// currentVal.AuxInt = lastMemReturnIdx
				// That might unnecessary. The correct location
				// is automatically obtained from func signature
				lastMem = currentVal
				continue
			}

			if currentVal.Op == OpStore {
				lastMem = currentVal
			}

			// There don't seem to be any Values with more than 4 arguments.
			// Statically allocate an array to fit them on the stack
			var argsDf [5]*Value
			for ai := 0; ai < len(currentVal.Args); ai++ {
				dfArr := firstBlock.NewValue2(valuePos, OpLocalAddr,
					types.NewPtr(arrayType), sp, lastMem)
				argDfPtr := firstBlock.NewValue2(valuePos, OpPtrIndex, arrayType,
					dfArr, f.ConstInt32(int32Type, int32(currentVal.Args[ai].ID)))
				argsDf[ai] = firstBlock.NewValue2(valuePos, OpLoad, intType, argDfPtr, lastMem)
			}

			// Bitwise or two dataflow bitmaps at a time
			firstArg := argsDf[0]
			for ai := 1; ai < len(currentVal.Args); ai++ {
				firstArg = firstBlock.NewValue2(valuePos, OpOr64, intType,
					firstArg, argsDf[ai])
			}

			// Store back the dataflow bitmap
			dfArr := firstBlock.NewValue2(valuePos, OpLocalAddr,
				types.NewPtr(arrayType), sp, lastMem)
			argDfPtr := firstBlock.NewValue2(valuePos, OpPtrIndex, arrayType,
				dfArr, f.ConstInt32(int32Type, int32(currentVal.ID)))
			lastMem = firstBlock.NewValue3A(valuePos, OpStore, types.TypeMem, intType,
				argDfPtr, firstArg, lastMem)
		}

		// for i := 0; i < len(firstBlock.Values); i++ {
		// 	v := firstBlock.Values[i]
		// 	log.Println(v.LongString())
		// 	log.Println(v.Type)
		// }
	}
}
