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
		for bidx := 0; bidx < len(f.Blocks); bidx++ {
			currentBlock := f.Blocks[bidx]
			initialValues := currentBlock.Values[:]

			for vidx := 0; vidx < len(initialValues); vidx++ {
				currentVal := initialValues[vidx]

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
		}
	} else {

		log.Println("Cool!")
		firstBlock := f.Blocks[0]
		// mem := firstBlock.Values[0]
		sp := firstBlock.Values[1]
		fbInitialValues := firstBlock.Values[:]

		// Create array to hold the dataflow values
		intType := types.Types[types.TINT]
		int32Type := types.Types[types.TINT32]

		argNameStrToDfIdx := make(map[string]int32)

		// Keep track of memory to maintain memory order
		var lastMem *Value

		// Search for dataflow array name
		var dfArrName *ir.Name
		var dfArrType *types.Type
		for vidx := 0; vidx < len(fbInitialValues); vidx++ {
			currentVal := fbInitialValues[vidx]
			if currentVal.Op == OpLocalAddr {
				valName, ok := currentVal.Aux.(*ir.Name)
				if ok {
					if valName.Sym().Name == "__dataflow_arr" {
						dfArrName = valName
						dfArrType = valName.Type()

						// This is the zeroing of the array
						lastMem = fbInitialValues[vidx+1]
						break
					}
				}
			}
		}
		if dfArrName == nil {
			log.Fatalln("__dataflow_arr not found at function start")
		}

		blockQueue := make([]*Block, 0)
		visitedBlock := make(map[*Block]bool)
		lastMemOfBlock := make(map[*Block]*Value)

		blockQueue = append(blockQueue, firstBlock)
		for len(blockQueue) != 0 {
			currentBlock := blockQueue[0]
			if visitedBlock[currentBlock] {
				blockQueue = blockQueue[1:]
				continue
			}
			visitedBlock[currentBlock] = true
			blockQueue = blockQueue[1:]

			// Only add a block to queue if all its dependencies have been visited
			// It's a topological sort to ensure all predecessor blocks have been processed
			// and their memory values obtained before processing a block
			for _, succ := range currentBlock.Succs {
				allPredsVisited := true
				tempBlock := succ.Block()
				for _, pred := range tempBlock.Preds {
					if !visitedBlock[pred.Block()] {
						allPredsVisited = false
						break
					}
				}
				if allPredsVisited {
					blockQueue = append(blockQueue, tempBlock)
				}
			}

			initialValues := currentBlock.Values[:]

			// Check if mem Phi exists
			// If not, create one
			memPhiExists := false
			for vidx := 0; vidx < len(initialValues); vidx++ {
				currentVal := initialValues[vidx]

				if currentVal.Op == OpPhi && currentVal.Type.IsMemory() {
					// For phi value, we need to change the memory vars after dataflow analysis
					currentVal.resetArgs()
					for argsidx := 0; argsidx < len(currentBlock.Preds); argsidx++ {
						predBlock := currentBlock.Preds[argsidx].Block()
						currentVal.AddArg(lastMemOfBlock[predBlock])
					}
					memPhiExists = true
					lastMem = currentVal
					break
				}
			}
			if !memPhiExists {
				memPhi := currentBlock.NewValue0(src.NoXPos, OpPhi, types.TypeMem)
				for argsidx := 0; argsidx < len(currentBlock.Preds); argsidx++ {
					predBlock := currentBlock.Preds[argsidx].Block()
					memPhi.AddArg(lastMemOfBlock[predBlock])
				}
				lastMem = memPhi
			}

			// Walk through the value and propagate dataflow based on their parameters
			for vidx := 0; vidx < len(initialValues); vidx++ {
				currentVal := initialValues[vidx]
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

						dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
							types.NewPtr(dfArrType), dfArrName, sp, lastMem)
						argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
							dfArr, f.ConstInt32(int32Type, origArgID))
						lastMem = currentBlock.NewValue3A(valuePos, OpStore, types.TypeMem, intType,
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
						dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
							types.NewPtr(dfArrType), dfArrName, sp, lastMem)
						argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
							dfArr, f.ConstInt32(int32Type, int32(arg1.ID)))
						resDf[argidx] = currentBlock.NewValue2(valuePos, OpLoad, intType, argDfPtr, lastMem)
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
						dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
							types.NewPtr(dfArrType), dfArrName, sp, lastMem)
						argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
							dfArr, f.ConstInt32(int32Type, int32(arg1.ID)))
						argDf[argidx] = currentBlock.NewValue2(valuePos, OpLoad, intType, argDfPtr, lastMem)
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
					nextVal := initialValues[vidx+retidx]
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
						nextVal = initialValues[vidx+retidx]
					}
					vidx = vidx + retidx - 1
					// The -1 is necessary as the coutner will be incremented at the end of loop

					dfValues := make([]*Value, numRealResults)
					for retidx, retVal := range realReturnValues {
						// Use currentVal here as that is the function call
						dfValues[retidx] = currentBlock.NewValue1I(valuePos, OpSelectN, intType,
							retVal.AuxInt+numRealResults, currentVal)
					}

					// After accepting all returns, store the df values to the dataflow array
					for retidx, retVal := range realReturnValues {
						dfVal := dfValues[retidx]

						dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
							types.NewPtr(dfArrType), dfArrName, sp, lastMem)
						argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
							dfArr, f.ConstInt32(int32Type, int32(retVal.ID)))
						lastMem = currentBlock.NewValue3A(valuePos, OpStore, types.TypeMem, intType,
							argDfPtr, dfVal, lastMem)
					}

					continue
				}

				// TODO: Need to handle stores (OpStore) separately.
				// Pass dataflow through the stored data
				if currentVal.Type.IsMemory() {
					lastMem = currentVal
				}

				// There don't seem to be any Values with more than 4 arguments.
				// Statically allocate an array to fit them on the stack
				var argsDf [5]*Value
				for argidx := 0; argidx < len(currentVal.Args); argidx++ {
					dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
						types.NewPtr(dfArrType), dfArrName, sp, lastMem)
					argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
						dfArr, f.ConstInt32(int32Type, int32(currentVal.Args[argidx].ID)))
					argsDf[argidx] = currentBlock.NewValue2(valuePos, OpLoad, intType, argDfPtr, lastMem)
				}

				// Bitwise or two dataflow bitmaps at a time
				firstArg := argsDf[0]
				for argidx := 1; argidx < len(currentVal.Args); argidx++ {
					firstArg = currentBlock.NewValue2(valuePos, OpOr64, intType,
						firstArg, argsDf[argidx])
				}

				// Store back the dataflow bitmap
				dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
					types.NewPtr(dfArrType), dfArrName, sp, lastMem)
				argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
					dfArr, f.ConstInt32(int32Type, int32(currentVal.ID)))
				lastMem = currentBlock.NewValue3A(valuePos, OpStore, types.TypeMem, intType,
					argDfPtr, firstArg, lastMem)
			}

			lastMemOfBlock[currentBlock] = lastMem
		}
	}
}
