package ssa

import (
	"cmd/compile/internal/ir"
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"log"
	"strings"
)

func dataflowInstrument(f *Func) {
	if strings.HasPrefix(f.Name, "DfMark") {
		log.Println("Yippeee!! " + f.Name)
	}

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
						argDf[argidx] = f.ConstInt64(types.Types[types.TINT64], 0)
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

		log.Println("Cool! " + f.Name)
		firstBlock := f.Blocks[0]
		// mem := firstBlock.Values[0]
		sp := firstBlock.Values[1]
		fbInitialValues := firstBlock.Values[:]

		// Create array to hold the dataflow values
		dfBmType := types.Types[types.TINT64]
		int32Type := types.Types[types.TINT32]

		argNameStrToDfIdx := make(map[string]int32)

		// Keep track of memory to maintain memory order
		var lastMem *Value

		// Search for dataflow array name
		var dfArrName *ir.Name
		var dfArrType *types.Type
		var blockDfName *ir.Name
		var blockDfType *types.Type
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

						// Next val after the zero should be the block dataflow array
						blockDfName = fbInitialValues[vidx+2].Aux.(*ir.Name)
						blockDfType = blockDfName.Type()

						lastMem = fbInitialValues[vidx+3]

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

			// log.Println(currentBlock.ID)
			// log.Println(currentBlock.Kind)
			// log.Println(currentBlock.Controls)

			// Only add a block to queue if all its dependencies have been visited
			// OLD: It's a topological sort to ensure all predecessor blocks have been processed
			// and their memory values obtained before processing a block
			// NEW: topological sort isn't necessary as we populate all Phis with lastMem
			// after all blocks have been processed
			for _, succ := range currentBlock.Succs {
				blockQueue = append(blockQueue, succ.Block())
			}

			initialValues := currentBlock.Values[:]

			// DEBUG stuff
			// for vidx := 0; vidx < len(initialValues); vidx++ {
			// 	currentVal := initialValues[vidx]
			// 	if currentVal.Op == OpMakeResult {
			// 		log.Println(currentVal.Op)
			// 		log.Println(currentVal.Args)
			// 	}
			// }

			// Check if mem Phi or Copy exist
			// If not, create one
			// IMPORTANT that this happens first
			// POPULATES last mem
			if len(currentBlock.Preds) > 0 {
				memPhiExists := false
				for vidx := 0; vidx < len(initialValues); vidx++ {
					currentVal := initialValues[vidx]

					if (currentVal.Op == OpPhi || currentVal.Op == OpCopy) && currentVal.Type.IsMemory() {
						// For phi value, we need to change the memory vars after dataflow analysis
						currentVal.resetArgs()
						// Actually populate the value later. Just make sure they exist for now
						//
						// for argsidx := 0; argsidx < len(currentBlock.Preds); argsidx++ {
						// 	predBlock := currentBlock.Preds[argsidx].Block()
						// 	currentVal.AddArg(lastMemOfBlock[predBlock])
						// }
						memPhiExists = true
						lastMem = currentVal
						break
					}
				}
				if !memPhiExists {
					opToUse := OpPhi
					if len(currentBlock.Preds) == 1 {
						opToUse = OpCopy
					}
					memPhi := currentBlock.NewValue0(src.NoXPos, opToUse, types.TypeMem)
					// for argsidx := 0; argsidx < len(currentBlock.Preds); argsidx++ {
					// 	predBlock := currentBlock.Preds[argsidx].Block()
					// 	memPhi.AddArg(lastMemOfBlock[predBlock])
					// }
					lastMem = memPhi
				}
			}

			// Get control values for all predecessors
			var predsDf [6]*Value
			for predidx, pred := range currentBlock.Preds {
				dfArr := currentBlock.NewValue2A(src.NoXPos, OpLocalAddr,
					types.NewPtr(blockDfType), blockDfName, sp, lastMem)
				argDfPtr := currentBlock.NewValue2(src.NoXPos, OpPtrIndex, dfArrType,
					dfArr, f.ConstInt32(int32Type, int32(pred.Block().ID)))
				predsDf[predidx] = currentBlock.NewValue2(src.NoXPos, OpLoad, dfBmType, argDfPtr, lastMem)
			}
			// Bitwise or two dataflow bitmaps at a time
			currentBlockDf := f.ConstInt64(int32Type, int64(0)) // Default to 0 if block has no predecessors
			for predidx := 0; predidx < len(currentBlock.Preds); predidx++ {
				currentBlockDf = currentBlock.NewValue2(src.NoXPos, OpOr64, dfBmType,
					currentBlockDf, predsDf[predidx])
			}

			var makeResultValue *Value

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
						lastMem = currentBlock.NewValue3A(valuePos, OpStore, types.TypeMem, dfBmType,
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
						resDf[argidx] = currentBlock.NewValue2(valuePos, OpLoad, dfBmType, argDfPtr, lastMem)
					}

					prevRealArgs := make([]*Value, numPrevRealArgs)
					copy(prevRealArgs, currentVal.Args[:numPrevRealArgs])
					currentVal.resetArgs()
					currentVal.AddArgs(prevRealArgs...)
					currentVal.AddArgs(resDf...)
					// currentVal.AddArgs(lastMem) // We do this at the end of the block
					// After the block df has been recorded
					// Take care to pass the mem parameter from new zero/alloc/store instructions
					// NOT the old one

					makeResultValue = currentVal

					continue
				}

				if currentVal.Op == OpStaticLECall {

					auxCall := currentVal.Aux.(*AuxCall)

					if auxCall == nil {
						continue
					}

					log.Println("dumpty " + auxCall.Fn.Name)
					if strings.HasPrefix(auxCall.Fn.Name, "runtime.DfMark") {
						// reset the mem value of this static call
						numRealArgs := len(currentVal.Args) - 1
						realArgs := make([]*Value, numRealArgs)
						copy(realArgs, currentVal.Args[:numRealArgs])
						currentVal.resetArgs()
						currentVal.AddArgs(realArgs...)
						currentVal.AddArgs(lastMem)

						retidx := 1
						nextVal := initialValues[vidx+retidx]
						var markerIdx, retVal *Value // Index of bit to set in the bitmap
						for nextVal.Op == OpSelectN {
							if nextVal.Type == types.TypeMem {
								lastMem = nextVal
							} else if nextVal.AuxInt == 0 {
								// That's the first return value
								retVal = nextVal
							} else if nextVal.AuxInt == 1 {
								// That's the second return value
								markerIdx = nextVal
							}

							retidx++
							nextVal = initialValues[vidx+retidx]
						}
						vidx = vidx + retidx - 1

						if retVal == nil {
							log.Fatalln("First return value from DfMark is not used")
						}

						if markerIdx == nil {
							markerIdx = currentBlock.NewValue1I(valuePos, OpSelectN, dfBmType,
								1, currentVal)
						}

						dfVal := currentBlock.NewValue2(valuePos, OpLsh64x64, dfBmType,
							f.ConstInt64(dfBmType, int64(1)), markerIdx)

						// Store the dataflow bitmap
						// Set the bitmap for both the passed in argument and return
						// There were problems with propagation when the argument and return are only
						// operated on by constant values
						arg1 := realArgs[1] // The first arg is a dict, that exists for generic function calls
						dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
							types.NewPtr(dfArrType), dfArrName, sp, lastMem)
						argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
							dfArr, f.ConstInt32(int32Type, int32(arg1.ID)))
						lastMem = currentBlock.NewValue3A(valuePos, OpStore, types.TypeMem, dfBmType,
							argDfPtr, dfVal, lastMem)

						dfArr = currentBlock.NewValue2A(valuePos, OpLocalAddr,
							types.NewPtr(dfArrType), dfArrName, sp, lastMem)
						argDfPtr = currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
							dfArr, f.ConstInt32(int32Type, int32(retVal.ID)))
						lastMem = currentBlock.NewValue3A(valuePos, OpStore, types.TypeMem, dfBmType,
							argDfPtr, dfVal, lastMem)

						continue
					} else if strings.HasPrefix(auxCall.Fn.Name, "runtime.DfInspect") {
						// reset the mem value of this static call
						numRealArgs := len(currentVal.Args) - 1
						realArgs := make([]*Value, numRealArgs)
						copy(realArgs, currentVal.Args[:numRealArgs])
						currentVal.resetArgs()
						currentVal.AddArgs(realArgs...)
						currentVal.AddArgs(lastMem)

						// Replace the first return by the dataflow value of the first Arg
						retidx := 1
						nextVal := initialValues[vidx+retidx]
						var retVal *Value // Index of bit to set in the bitmap
						for nextVal.Op == OpSelectN {
							if nextVal.Type == types.TypeMem {
								lastMem = nextVal
							} else if nextVal.AuxInt == 0 {
								// That's the first return value
								retVal = nextVal
							}

							retidx++
							nextVal = initialValues[vidx+retidx]
						}
						vidx = vidx + retidx - 1

						arg1 := realArgs[1] // The first arg is a dict, that exists for generic function calls
						dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
							types.NewPtr(dfArrType), dfArrName, sp, lastMem)
						argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
							dfArr, f.ConstInt32(int32Type, int32(arg1.ID)))
						// argDf[argidx] = currentBlock.NewValue2(valuePos, OpLoad, dfBmType, argDfPtr, lastMem)
						// Basically replace a return with the above load
						retVal.reset(OpLoad)
						retVal.AddArgs(argDfPtr, lastMem)

						continue
					}

					// For call from dataflow to non dataflow functions
					// Don't do anything
					if !auxCall.Dataflow {
						continue
					}

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
						argDf[argidx] = currentBlock.NewValue2(valuePos, OpLoad, dfBmType, argDfPtr, lastMem)
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
						dfValues[retidx] = currentBlock.NewValue1I(valuePos, OpSelectN, dfBmType,
							retVal.AuxInt+numRealResults, currentVal)
					}

					// After accepting all returns, store the df values to the dataflow array
					for retidx, retVal := range realReturnValues {
						dfVal := dfValues[retidx]

						dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
							types.NewPtr(dfArrType), dfArrName, sp, lastMem)
						argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
							dfArr, f.ConstInt32(int32Type, int32(retVal.ID)))
						lastMem = currentBlock.NewValue3A(valuePos, OpStore, types.TypeMem, dfBmType,
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
				for argidx, currentarg := range currentVal.Args {
					dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
						types.NewPtr(dfArrType), dfArrName, sp, lastMem)
					argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
						dfArr, f.ConstInt32(int32Type, int32(currentarg.ID)))
					argsDf[argidx] = currentBlock.NewValue2(valuePos, OpLoad, dfBmType, argDfPtr, lastMem)
				}

				// Bitwise or two dataflow bitmaps at a time
				firstArg := currentBlockDf
				for argidx := 0; argidx < len(currentVal.Args); argidx++ {
					firstArg = currentBlock.NewValue2(valuePos, OpOr64, dfBmType,
						firstArg, argsDf[argidx])
				}

				// Store back the dataflow bitmap
				dfArr := currentBlock.NewValue2A(valuePos, OpLocalAddr,
					types.NewPtr(dfArrType), dfArrName, sp, lastMem)
				argDfPtr := currentBlock.NewValue2(valuePos, OpPtrIndex, dfArrType,
					dfArr, f.ConstInt32(int32Type, int32(currentVal.ID)))
				lastMem = currentBlock.NewValue3A(valuePos, OpStore, types.TypeMem, dfBmType,
					argDfPtr, firstArg, lastMem)
			}

			// There don't seem to be any Values with more than 4 arguments.
			// Statically allocate an array to fit them on the stack
			var ctrlDf [4]*Value
			ctrlValues := currentBlock.ControlValues()
			for ctrlidx, ctrl := range ctrlValues {
				dfArr := currentBlock.NewValue2A(currentBlock.Pos, OpLocalAddr,
					types.NewPtr(dfArrType), dfArrName, sp, lastMem)
				argDfPtr := currentBlock.NewValue2(currentBlock.Pos, OpPtrIndex, dfArrType,
					dfArr, f.ConstInt32(int32Type, int32(ctrl.Args[ctrlidx].ID)))
				ctrlDf[ctrlidx] = currentBlock.NewValue2(currentBlock.Pos, OpLoad, dfBmType, argDfPtr, lastMem)
			}

			// Bitwise or two dataflow bitmaps at a time
			for ctrlidx := 0; ctrlidx < len(ctrlValues); ctrlidx++ {
				currentBlockDf = currentBlock.NewValue2(currentBlock.Pos, OpOr64, dfBmType,
					currentBlockDf, ctrlDf[ctrlidx])
			}

			// Store back the dataflow bitmap
			dfArr := currentBlock.NewValue2A(currentBlock.Pos, OpLocalAddr,
				types.NewPtr(blockDfType), blockDfName, sp, lastMem)
			argDfPtr := currentBlock.NewValue2(currentBlock.Pos, OpPtrIndex, dfArrType,
				dfArr, f.ConstInt32(int32Type, int32(currentBlock.ID)))
			lastMem = currentBlock.NewValue3A(currentBlock.Pos, OpStore, types.TypeMem, dfBmType,
				argDfPtr, currentBlockDf, lastMem)

			lastMemOfBlock[currentBlock] = lastMem

			if makeResultValue != nil {
				makeResultValue.AddArgs(lastMem)
				makeResultValue = nil
			}
		}

		// For memory phi/copy value, we need to change the memory vars after dataflow analysis
		// Actually populate the values now that we know the last mem of all blocks
		for _, currentBlock := range f.Blocks {
			for _, currentVal := range currentBlock.Values {
				if (currentVal.Op == OpPhi || currentVal.Op == OpCopy) && currentVal.Type.IsMemory() {
					for _, pred := range currentBlock.Preds {
						predBlock := pred.Block()
						currentVal.AddArg(lastMemOfBlock[predBlock])
					}
					break
				}
			}
		}
	}
}
