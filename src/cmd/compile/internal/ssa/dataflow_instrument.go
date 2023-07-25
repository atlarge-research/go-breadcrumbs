package ssa

import (
	"cmd/compile/internal/ir"
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"log"
	"strings"
)

func dataflowInstrument(f *Func) {
	if !f.Dataflow {
		firstBlock := f.Blocks[0]
		initialValues := firstBlock.Values[:]

		for vi := 0; vi < len(initialValues); vi++ {
			currentVal := initialValues[vi]

			// Need to shim function calls from
			// non-dataflow code to dataflow code
			if currentVal.Op == OpStaticLECall {
				// No need to change type for this.
				// Type was obtained automatically after
				// func signature modification

				auxCall := currentVal.Aux.(*AuxCall)
				// For some calls, auxCall is nil, figure out why
				if auxCall == nil || !auxCall.Dataflow {
					continue
				}

				numRealArgs := int64(len(currentVal.Args) - 1)
				// len-1 because last arg is memory location
				argDf := make([]*Value, numRealArgs)
				for argidx := int64(0); argidx < numRealArgs; argidx++ {
					argDf[argidx] = f.ConstInt32(types.Types[types.TINT32], 0)
				}

				realArgs := make([]*Value, numRealArgs)
				lastMem := currentVal.Args[numRealArgs]
				copy(realArgs, currentVal.Args[:numRealArgs])
				currentVal.resetArgs()
				currentVal.AddArgs(realArgs...)
				currentVal.AddArgs(argDf...)
				currentVal.AddArgs(lastMem)

				// NO NEED TO DEAL WITH RETURNS

				continue
			}
		}
	} else {
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

		argNameStrToDfIdx := make(map[string]int32)

		types.CalcSizeDisabled = true

		// Walk through the value and propagate dataflow based on their parameters
		for vi := 0; vi < len(initialValues); vi++ {
			currentVal := initialValues[vi]
			valuePos := currentVal.Pos

			if currentVal.Op == OpArg {
				argName := currentVal.Aux.(*ir.Name)
				argSym := argName.Sym()
				argNameStr := argSym.Name

				if !strings.HasPrefix(argNameStr, "_df_") {
					// normal arg
					argNameStrToDfIdx[argNameStr] = int32(currentVal.ID)
				} else {
					// Dataflow arg
					// Normal always comes first and the map is populated
					origArgName := strings.Trim(argNameStr, "_df_")
					origArgID := argNameStrToDfIdx[origArgName]

					dfArr := firstBlock.NewValue2(valuePos, OpLocalAddr,
						types.NewPtr(arrayType), sp, lastMem)
					argDfPtr := firstBlock.NewValue2(valuePos, OpPtrIndex, arrayType,
						dfArr, f.ConstInt32(int32Type, origArgID))
					lastMem = firstBlock.NewValue3A(valuePos, OpStore, types.TypeMem, intType,
						argDfPtr, currentVal, lastMem)
				}

				continue
			}

			// This like memory init, sp init, args dont need to be tracked
			if len(currentVal.Args) < 1 {
				continue
			}

			if currentVal.Op == OpMakeResult {
				numPrevRealArgs := (len(currentVal.Args) - 1) / 2
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

				continue
			}

			if currentVal.Op == OpStaticLECall {
				// No need to change type for this.
				// Type was obtained automatically after
				// func signature modification

				numRealArgs := int64(len(currentVal.Args) - 1)
				// len-1 because last arg is memory location
				argDf := make([]*Value, numRealArgs)
				for argidx := int64(0); argidx < numRealArgs; argidx++ {
					arg1 := currentVal.Args[argidx]
					dfArr := firstBlock.NewValue2(valuePos, OpLocalAddr,
						types.NewPtr(arrayType), sp, lastMem)
					argDfPtr := firstBlock.NewValue2(valuePos, OpPtrIndex, arrayType,
						dfArr, f.ConstInt32(int32Type, int32(arg1.ID)))
					argDf[argidx] = firstBlock.NewValue2(valuePos, OpLoad, intType, argDfPtr, lastMem)
				}

				realArgs := make([]*Value, numRealArgs)
				copy(realArgs, currentVal.Args[:numRealArgs])
				currentVal.resetArgs()
				currentVal.AddArgs(realArgs...)
				currentVal.AddArgs(argDf...)
				currentVal.AddArgs(lastMem)

				lastMem = currentVal

				resultsType := currentVal.Type
				numResults := resultsType.NumFields()
				numRealResults := int64((numResults - 1) / 2)

				// Process return values
				realReturnValues := make([]*Value, numRealResults)
				retidx := 1
				nextVal := initialValues[vi+retidx]
				for nextVal.Op == OpSelectN {
					if nextVal.Type == types.TypeMem {
						// The correct memory location in the return
						// is automatically obtained from func signature
						lastMem = nextVal
					} else {
						// Store these returns in the map
						// For later stores to the df array
						// -1 because we start with 1
						// Another -1 because of mem type return
						realReturnValues[nextVal.AuxInt] = nextVal
					}

					retidx++
					nextVal = initialValues[vi+retidx]
				}
				vi = vi + retidx - 1
				// The -1 is necessary as the coutner will be incremented at the end of loop

				dfValues := make([]*Value, numRealResults)
				for retidx, retVal := range realReturnValues {
					// Use currentVal here as that is the function call
					dfValues[retidx] = firstBlock.NewValue1I(valuePos, OpSelectN, intType,
						retVal.AuxInt+numRealResults, currentVal)
				}

				// After accepting all returns, store the df values to the dataflow array
				for retidx, retVal := range realReturnValues {
					dfVal := dfValues[retidx]

					dfArr := firstBlock.NewValue2(valuePos, OpLocalAddr,
						types.NewPtr(arrayType), sp, lastMem)
					argDfPtr := firstBlock.NewValue2(valuePos, OpPtrIndex, arrayType,
						dfArr, f.ConstInt32(int32Type, int32(retVal.ID)))
					lastMem = firstBlock.NewValue3A(valuePos, OpStore, types.TypeMem, intType,
						argDfPtr, dfVal, lastMem)
				}

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
