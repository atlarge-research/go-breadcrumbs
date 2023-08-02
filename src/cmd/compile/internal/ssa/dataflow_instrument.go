package ssa

import (
	"cmd/compile/internal/ir"
	"cmd/compile/internal/types"
	"cmd/internal/src"
	"log"
	"strings"
)

var dfBmType *types.Type
var int32Type *types.Type

type dfInstrumentState struct {
	f *Func

	// Keep track of memory to maintain memory order
	lastMem        *Value
	sp             *Value
	currentBlock   *Block
	currentBlockDf *Value
	initialValues  []*Value

	dfArrName   *ir.Name
	dfArrType   *types.Type
	blockDfName *ir.Name
	blockDfType *types.Type

	argNameStrToDfIdx map[string]int32
}

func (d *dfInstrumentState) init() {
	dfBmType = types.Types[types.TINT64]
	int32Type = types.Types[types.TINT32]

	firstBlock := d.f.Blocks[0]
	d.sp = firstBlock.Values[1]
	d.argNameStrToDfIdx = make(map[string]int32)
}

func (d *dfInstrumentState) findDfArrays() {
	firstBlock := d.f.Blocks[0]
	fbInitialValues := firstBlock.Values[:]

	// Search for dataflow array name
	for vidx := 0; vidx < len(fbInitialValues); vidx++ {
		currentVal := fbInitialValues[vidx]
		if currentVal.Op == OpLocalAddr {
			valName, ok := currentVal.Aux.(*ir.Name)
			if ok {
				if valName.Sym().Name == "__dataflow_arr" {
					d.dfArrName = valName
					d.dfArrType = valName.Type()

					// This is the zeroing of the array
					// d.lastMem = fbInitialValues[vidx+1]

					// Next val after the zero should be the block dataflow array
					d.blockDfName = fbInitialValues[vidx+2].Aux.(*ir.Name)
					d.blockDfType = d.blockDfName.Type()

					d.lastMem = fbInitialValues[vidx+3]

					break
				}
			}
		}
	}
	if d.dfArrName == nil {
		log.Fatalln("__dataflow_arr not found at function start")
	}
}

func (d *dfInstrumentState) visitBlocks() {
	blockQueue := make([]*Block, 0)
	visitedBlock := make(map[*Block]bool)
	lastMemOfBlock := make(map[*Block]*Value)

	blockQueue = append(blockQueue, d.f.Blocks[0])
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
					d.lastMem = currentVal
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
				d.lastMem = memPhi
			}
		}

		// Get control values for all predecessors
		var predsDf [6]*Value
		for predidx, pred := range currentBlock.Preds {
			dfArr := currentBlock.NewValue2A(src.NoXPos, OpLocalAddr,
				types.NewPtr(d.blockDfType), d.blockDfName, d.sp, d.lastMem)
			argDfPtr := currentBlock.NewValue2(src.NoXPos, OpPtrIndex, d.dfArrType,
				dfArr, d.f.ConstInt32(int32Type, int32(pred.Block().ID)))
			predsDf[predidx] = currentBlock.NewValue2(src.NoXPos, OpLoad, dfBmType, argDfPtr, d.lastMem)
		}
		// Bitwise or two dataflow bitmaps at a time
		currentBlockDf := d.f.ConstInt64(int32Type, int64(0)) // Default to 0 if block has no predecessors
		for predidx := 0; predidx < len(currentBlock.Preds); predidx++ {
			currentBlockDf = currentBlock.NewValue2(src.NoXPos, OpOr64, dfBmType,
				currentBlockDf, predsDf[predidx])
		}

		// Go over Values here
		d.currentBlock = currentBlock
		d.currentBlockDf = currentBlockDf
		d.initialValues = initialValues
		makeResultValue := d.visitValues()
		d.currentBlock = nil
		d.currentBlockDf = nil
		d.initialValues = nil

		var ctrlDf [4]*Value
		ctrlValues := currentBlock.ControlValues()
		for ctrlidx, ctrl := range ctrlValues {
			dfArr := currentBlock.NewValue2A(currentBlock.Pos, OpLocalAddr,
				types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
			argDfPtr := currentBlock.NewValue2(currentBlock.Pos, OpPtrIndex, d.dfArrType,
				dfArr, d.f.ConstInt32(int32Type, int32(ctrl.Args[ctrlidx].ID)))
			ctrlDf[ctrlidx] = currentBlock.NewValue2(currentBlock.Pos, OpLoad, dfBmType, argDfPtr, d.lastMem)
		}

		// Bitwise or two dataflow bitmaps at a time
		for ctrlidx := 0; ctrlidx < len(ctrlValues); ctrlidx++ {
			currentBlockDf = currentBlock.NewValue2(currentBlock.Pos, OpOr64, dfBmType,
				currentBlockDf, ctrlDf[ctrlidx])
		}

		// Store back the dataflow bitmap
		dfArr := currentBlock.NewValue2A(currentBlock.Pos, OpLocalAddr,
			types.NewPtr(d.blockDfType), d.blockDfName, d.sp, d.lastMem)
		argDfPtr := currentBlock.NewValue2(currentBlock.Pos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(currentBlock.ID)))
		d.lastMem = currentBlock.NewValue3A(currentBlock.Pos, OpStore, types.TypeMem, dfBmType,
			argDfPtr, currentBlockDf, d.lastMem)

		lastMemOfBlock[currentBlock] = d.lastMem

		if makeResultValue != nil {
			makeResultValue.AddArgs(d.lastMem)
			makeResultValue = nil
		}
	}

	// For memory phi/copy value, we need to change the memory vars after dataflow analysis
	// Actually populate the values now that we know the last mem of all blocks
	for _, currentBlock := range d.f.Blocks {
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

func (d *dfInstrumentState) visitValues() (makeResultValue *Value) {
	for vidx := 0; vidx < len(d.initialValues); vidx++ {
		currentVal := d.initialValues[vidx]

		if currentVal.Op == OpArg {
			d.extractDfOfArg(currentVal)

			continue
		}

		// This like memory init, sp init, args dont need to be tracked
		if len(currentVal.Args) < 1 {
			continue
		}

		if currentVal.Op == OpMakeResult {
			makeResultValue = d.addDfToReturn(currentVal)

			continue
		}

		if currentVal.Op == OpStaticLECall {

			auxCall := currentVal.Aux.(*AuxCall)

			if auxCall == nil {
				continue
			}

			log.Println("dumpty " + auxCall.Fn.Name)
			var isMarkInspect bool
			isMarkInspect, vidx = d.markInspectMachinery(currentVal, vidx)
			if isMarkInspect {
				continue
			}

			// For call from dataflow to non dataflow functions
			// Don't do anything
			if !auxCall.Dataflow {
				continue
			}

			vidx = d.functionCall(currentVal, vidx)
			continue
		}

		if currentVal.Op == OpLocalAddr ||
			currentVal.Op == OpOffPtr {

			// We deal with them in the Zero/Load/Store that follows
			continue
		}

		if currentVal.Op == OpZero {
			d.zeroMem(currentVal)
			continue
		}

		if currentVal.Op == OpLoad || currentVal.Op == OpStore {
			d.loadStore(currentVal, vidx)

			continue
		}

		if currentVal.Type.IsMemory() {
			d.lastMem = currentVal
		}

		d.propagateDfFromArgs(currentVal)
	}

	return makeResultValue
}

func (d *dfInstrumentState) extractDfOfArg(currentVal *Value) {
	valPos := currentVal.Pos
	argName := currentVal.Aux.(*ir.Name)
	argSym := argName.Sym()
	argNameStr := argSym.Name

	if !strings.HasPrefix(argNameStr, "_df_") {
		// normal arg
		d.argNameStrToDfIdx[argNameStr] = int32(currentVal.ID)
	} else {
		// Dataflow arg
		// Normal always comes first and the map is populated
		origArgName := strings.Trim(argNameStr, "_df_")
		origArgID := d.argNameStrToDfIdx[origArgName]

		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, origArgID))
		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			argDfPtr, currentVal, d.lastMem)
	}
}

func (d *dfInstrumentState) addDfToReturn(currentVal *Value) (makeResultValue *Value) {
	valPos := currentVal.Pos
	numPrevRealArgs := (len(currentVal.Args) - 1) / 2
	// len-1 because last arg is memory location
	resDf := make([]*Value, numPrevRealArgs)
	for argidx := 0; argidx < numPrevRealArgs; argidx++ {
		arg1 := currentVal.Args[argidx]
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(arg1.ID)))
		retvalDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, argDfPtr, d.lastMem)
		combinedDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			d.currentBlockDf, retvalDf)
		resDf[argidx] = combinedDf
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
	return makeResultValue
}

func (d *dfInstrumentState) markInspectMachinery(currentVal *Value, vidx int) (bool, int) {
	auxCall := currentVal.Aux.(*AuxCall)
	valPos := currentVal.Pos

	if strings.HasPrefix(auxCall.Fn.Name, "runtime.DfMark") {
		// reset the mem value of this static call
		numRealArgs := len(currentVal.Args) - 1
		realArgs := make([]*Value, numRealArgs)
		copy(realArgs, currentVal.Args[:numRealArgs])
		currentVal.resetArgs()
		currentVal.AddArgs(realArgs...)
		currentVal.AddArgs(d.lastMem)

		retidx := 1
		nextVal := d.initialValues[vidx+retidx]
		var markerIdx, retVal *Value // Index of bit to set in the bitmap
		for nextVal.Op == OpSelectN {
			if nextVal.Type.IsMemory() {
				d.lastMem = nextVal
			} else if nextVal.AuxInt == 0 {
				// That's the first return value
				retVal = nextVal
			} else if nextVal.AuxInt == 1 {
				// That's the second return value
				markerIdx = nextVal
			}

			retidx++
			nextVal = d.initialValues[vidx+retidx]
		}
		vidx = vidx + retidx - 1

		if retVal == nil {
			log.Fatalln("First return value from DfMark is not used")
		}

		if markerIdx == nil {
			markerIdx = d.currentBlock.NewValue1I(valPos, OpSelectN, dfBmType,
				1, currentVal)
		}

		dfVal := d.currentBlock.NewValue2(valPos, OpLsh64x64, dfBmType,
			d.f.ConstInt64(dfBmType, int64(1)), markerIdx)

		// Store the dataflow bitmap
		// Set the bitmap for both the passed in argument and return
		// There were problems with propagation when the argument and return are only
		// operated on by constant values
		arg1 := realArgs[1] // The first arg is a dict, that exists for generic function calls
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(arg1.ID)))
		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			argDfPtr, dfVal, d.lastMem)

		dfArr = d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr = d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(retVal.ID)))
		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			argDfPtr, dfVal, d.lastMem)

		return true, vidx
	} else if strings.HasPrefix(auxCall.Fn.Name, "runtime.DfInspect") {
		// reset the mem value of this static call
		numRealArgs := len(currentVal.Args) - 1
		realArgs := make([]*Value, numRealArgs)
		copy(realArgs, currentVal.Args[:numRealArgs])
		currentVal.resetArgs()
		currentVal.AddArgs(realArgs...)
		currentVal.AddArgs(d.lastMem)

		// Replace the first return by the dataflow value of the first Arg
		retidx := 1
		nextVal := d.initialValues[vidx+retidx]
		var retVal *Value // Index of bit to set in the bitmap
		for nextVal.Op == OpSelectN {
			if nextVal.Type.IsMemory() {
				d.lastMem = nextVal
			} else if nextVal.AuxInt == 0 {
				// That's the first return value
				retVal = nextVal
			}

			retidx++
			nextVal = d.initialValues[vidx+retidx]
		}
		vidx = vidx + retidx - 1

		arg1 := realArgs[1] // The first arg is a dict, that exists for generic function calls
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(arg1.ID)))
		// argDf[argidx] = currentBlock.NewValue2(valuePos, OpLoad, dfBmType, argDfPtr, lastMem)
		// Basically replace a return with the above load
		retVal.reset(OpLoad)
		retVal.AddArgs(argDfPtr, d.lastMem)

		return true, vidx
	}

	return false, vidx
}

func (d *dfInstrumentState) functionCall(currentVal *Value, vidx int) int {
	// No need to change type for this.
	// Type was obtained automatically after
	// func signature modification

	valPos := currentVal.Pos

	numRealArgs := int64(len(currentVal.Args) - 1)
	// len-1 because last arg is memory location
	argDf := make([]*Value, numRealArgs)
	for argidx := int64(0); argidx < numRealArgs; argidx++ {
		arg1 := currentVal.Args[argidx]
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(arg1.ID)))
		paramDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, argDfPtr, d.lastMem)
		combinedDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			d.currentBlockDf, paramDf)
		argDf[argidx] = combinedDf
	}

	realArgs := make([]*Value, numRealArgs)
	copy(realArgs, currentVal.Args[:numRealArgs])
	currentVal.resetArgs()
	currentVal.AddArgs(realArgs...)
	currentVal.AddArgs(argDf...)
	currentVal.AddArgs(d.lastMem)

	d.lastMem = currentVal

	resultsType := currentVal.Type
	numResults := resultsType.NumFields()
	numRealResults := int64((numResults - 1) / 2)

	// Process return values
	realReturnValues := make([]*Value, numRealResults)
	retidx := 1
	nextVal := d.initialValues[vidx+retidx]
	for nextVal.Op == OpSelectN {
		if nextVal.Type.IsMemory() {
			// The correct memory location in the return
			// is automatically obtained from func signature
			d.lastMem = nextVal
		} else {
			// Store these returns in the map
			// For later stores to the df array
			// -1 because we start with 1
			// Another -1 because of mem type return
			realReturnValues[nextVal.AuxInt] = nextVal
		}

		retidx++
		nextVal = d.initialValues[vidx+retidx]
	}
	vidx = vidx + retidx - 1
	// The -1 is necessary as the coutner will be incremented at the end of loop

	dfValues := make([]*Value, numRealResults)
	for retidx, retVal := range realReturnValues {
		// Use currentVal here as that is the function call
		retvalDf := d.currentBlock.NewValue1I(valPos, OpSelectN, dfBmType,
			retVal.AuxInt+numRealResults, currentVal)
		combinedDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			d.currentBlockDf, retvalDf)
		argDf[retidx] = combinedDf
	}

	// After accepting all returns, store the df values to the dataflow array
	for retidx, retVal := range realReturnValues {
		dfVal := dfValues[retidx]

		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(retVal.ID)))
		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			argDfPtr, dfVal, d.lastMem)
	}

	return vidx
}

func (d *dfInstrumentState) zeroMem(currentVal *Value) {
	zeroType := currentVal.Aux.(*types.Type)
	// Specifically for struct types, allocate additional
	// memory for dataflow propagation
	if zeroType != nil && zeroType.IsStruct() &&
		!zeroType.IsFuncArgStruct() {
		numFields := zeroType.NumComponents(true)
		additionalMem := numFields * dfBmType.Size()

		currentVal.AuxInt = currentVal.AuxInt + additionalMem
	}

	d.lastMem = currentVal
}

func (d *dfInstrumentState) loadStore(currentVal *Value, vidx int) {
	valPos := currentVal.Pos
	ptr := currentVal.Args[0]
	localAddr := ptr.Args[0]

	// (* Value).copyInto doesn't work when Value has mem args
	newLocalAddr := d.currentBlock.NewValue0(valPos, localAddr.Op, localAddr.Type)
	newLocalAddr.Aux = localAddr.Aux
	newLocalAddr.AuxInt = localAddr.AuxInt
	newLocalAddr.AddArgs(localAddr.Args[:len(localAddr.Args)-1]...)
	newLocalAddr.AddArgs(d.lastMem)

	fieldDfPtr := d.currentBlock.NewValue0(valPos, ptr.Op, types.NewPtr(dfBmType))
	fieldDfPtr.AddArgs(newLocalAddr)

	structName := localAddr.Aux.(*ir.Name)
	structType := structName.Type()
	baseSize := structType.Size()
	fieldDfPtr.AuxInt = baseSize + auxToInt64(ptr.Aux)*dfBmType.Size()

	prevArgs := make([]*Value, len(currentVal.Args))
	copy(prevArgs, currentVal.Args)
	currentVal.resetArgs()
	currentVal.AddArgs(prevArgs[:len(prevArgs)-1]...)
	currentVal.AddArgs(d.lastMem)

	if currentVal.Op == OpLoad {
		fieldDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, fieldDfPtr, d.lastMem)
		combinedDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			d.currentBlockDf, fieldDf)

		// Now store this dataflow to the array position of the Load statement
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(currentVal.ID)))
		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			argDfPtr, combinedDf, d.lastMem)
	} else {
		// This can only be OpStore
		// Propagate value from df array to the struct's df space

		d.lastMem = currentVal

		storeDataArg := currentVal.Args[1]

		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(storeDataArg.ID)))
		fieldDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, argDfPtr, d.lastMem)
		combinedDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			d.currentBlockDf, fieldDf)

		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			fieldDfPtr, combinedDf, d.lastMem)
	}
}

func (d *dfInstrumentState) propagateDfFromArgs(currentVal *Value) {
	valPos := currentVal.Pos

	// There don't seem to be any Values with more than 4 arguments.
	// Statically allocate an array to fit them on the stack
	var argsDf [5]*Value
	for argidx, currentarg := range currentVal.Args {
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
			dfArr, d.f.ConstInt32(int32Type, int32(currentarg.ID)))
		argsDf[argidx] = d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, argDfPtr, d.lastMem)
	}

	// Bitwise or two dataflow bitmaps at a time
	firstArg := d.currentBlockDf
	for argidx := 0; argidx < len(currentVal.Args); argidx++ {
		firstArg = d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			firstArg, argsDf[argidx])
	}

	// Store back the dataflow bitmap
	dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
		types.NewPtr(d.dfArrType), d.dfArrName, d.sp, d.lastMem)
	argDfPtr := d.currentBlock.NewValue2(valPos, OpPtrIndex, d.dfArrType,
		dfArr, d.f.ConstInt32(int32Type, int32(currentVal.ID)))
	d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
		argDfPtr, firstArg, d.lastMem)
}

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

		dis := &dfInstrumentState{f: f}
		dis.init()
		dis.findDfArrays()
		dis.visitBlocks()
	}
}
