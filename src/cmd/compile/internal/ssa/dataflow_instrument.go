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

	dfArrName        *ir.Name
	dfArrType        *types.Type
	blockDfName      *ir.Name
	blockDfType      *types.Type
	dfDeclId         ID
	blockDfZeroId    ID
	dfArrRetVal      *Value
	blockDfArrRetVal *Value

	argNameStrToDfIdx map[string]int64
	nameToDfPtr       map[string]*Value
	ptrToDfPtr        map[ID]*Value
	isPhiDfPtr        map[ID]bool
	safeDfPtrs        map[string]*Value
}

func (d *dfInstrumentState) init() {
	dfBmType = types.Types[types.TINT64]
	int32Type = types.Types[types.TINT32]

	firstBlock := d.f.Blocks[0]
	d.lastMem = firstBlock.Values[0]
	d.sp = firstBlock.Values[1]
	d.argNameStrToDfIdx = make(map[string]int64)
	d.nameToDfPtr = make(map[string]*Value)
	d.ptrToDfPtr = make(map[ID]*Value)
	d.isPhiDfPtr = make(map[ID]bool)
	d.safeDfPtrs = make(map[string]*Value)
}

func (d *dfInstrumentState) findDfArrays() {
	for name, values := range d.f.NamedValues {
		// Need the ampersand as this is an addr value
		if strings.HasPrefix(name.String(), "&__dfarrret_arr") {
			d.dfArrRetVal = values[0]
		}
		if strings.HasPrefix(name.String(), "&__blockdfarrret_arr") {
			d.blockDfArrRetVal = values[0]
		}
	}
	firstBlock := d.f.Blocks[0]
	fbInitialValues := firstBlock.Values[:]

	// Search for dataflow array name
	for vidx := 1; vidx < len(fbInitialValues); vidx++ {
		currentVal := fbInitialValues[vidx]

		if currentVal.Op == OpLocalAddr {
			valName, ok := currentVal.Aux.(*ir.Name)
			if ok {
				if valName.Sym().Name == "__dataflow_arr" {
					d.dfArrName = valName
					d.dfArrType = valName.Type()

					d.dfDeclId = currentVal.ID

					currentVal.resetArgs()
					currentVal.SetArgs2(d.sp, d.lastMem)
					d.resetMem(fbInitialValues[vidx+1]) //Zero

					vidx = vidx + 1
					continue
				} else if valName.Sym().Name == "__blockdf_arr" {
					d.blockDfName = valName
					d.blockDfType = valName.Type()

					blockDfZero := fbInitialValues[vidx+1]
					d.blockDfZeroId = blockDfZero.ID

					currentVal.resetArgs()
					currentVal.SetArgs2(d.sp, d.lastMem)
					d.resetMem(blockDfZero) //Zero

					vidx = vidx + 1
					break
				}
			}
		}

		// Any mem values that occur before df arr init
		// Need to be taken care of
		if currentVal.Type.IsMemory() {
			d.resetMem(currentVal)
		}
	}
	if d.dfArrName == nil {
		log.Fatalln("__dataflow_arr not found at function start")
	}
}

func (d *dfInstrumentState) visitBlocks() {
	lastMemOfBlock := make(map[*Block]*Value)

	// Initial blocks are used for checking if passed in dfptrs are nils
	// Skipping them
	// Blocks are supposed to be unordered. But assuming order at least for the first nil checks works
	for _, currentBlock := range d.f.Blocks {
		initialValues := currentBlock.Values[:]

		onlyParseArgsAndPassMem := false
		// Skip blocks which are just nil checks for passed in dfptrs
		// We do that by checking if the control values of a block and
		// the function itself don't have the same position
		// if dfPtrsExist && currentBlock.Pos.SameFileAndLine(firstBlock.Pos) {
		// 	// Parse args and pass through mem values
		// 	onlyParseArgsAndPassMem = true
		// }

		// Check if mem Phi or Copy exist
		// If not, create one
		// IMPORTANT that this happens first
		// POPULATES lastmem
		if len(currentBlock.Preds) > 0 {
			memPhiExists := false
			for vidx := 0; vidx < len(initialValues); vidx++ {
				currentVal := initialValues[vidx]

				if (currentVal.Op == OpPhi || currentVal.Op == OpCopy) && currentVal.Type.IsMemory() {
					// For phi value, we need to change the memory vars after dataflow analysis
					currentVal.resetArgs()
					// Actually populate the value later. Just make sure they exist for now

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
				d.lastMem = memPhi
			}
		}

		// Get control values for all predecessors
		var predsDf [6]*Value
		for predidx, pred := range currentBlock.Preds {
			dfArr := currentBlock.NewValue2A(currentBlock.Pos, OpLocalAddr,
				d.blockDfType.PtrTo(), d.blockDfName, d.sp, d.lastMem)
			argDfPtr := currentBlock.NewValue1I(currentBlock.Pos, OpOffPtr, dfBmType.PtrTo(),
				int64(pred.Block().ID)*dfBmType.Size(), dfArr)
			predsDf[predidx] = currentBlock.NewValue2(currentBlock.Pos, OpLoad, dfBmType, argDfPtr, d.lastMem)
		}
		// Bitwise or two dataflow bitmaps at a time
		currentBlockDf := d.f.ConstInt64(dfBmType, int64(0)) // Default to 0 if block has no predecessors
		for predidx := 0; predidx < len(currentBlock.Preds); predidx++ {
			currentBlockDf = currentBlock.NewValue2(src.NoXPos, OpOr64, dfBmType,
				currentBlockDf, predsDf[predidx])
		}

		// Go over Values here
		d.currentBlock = currentBlock
		d.currentBlockDf = currentBlockDf
		d.initialValues = initialValues
		var makeResultValue *Value
		if onlyParseArgsAndPassMem {
			d.onlyPassMem()
		} else {
			makeResultValue = d.visitValues()
		}
		d.currentBlock = nil
		// Could be read from Arg
		currentBlockDf = d.currentBlockDf
		d.currentBlockDf = nil
		d.initialValues = nil

		var ctrlDfs = make([]*Value, 0, 4)
		ctrlValues := currentBlock.ControlValues()
		for _, ctrl := range ctrlValues {
			if ctrl.Op == OpIsInBounds ||
				ctrl.Op == OpIsSliceInBounds {
				continue
			}

			dfArr := currentBlock.NewValue2A(currentBlock.Pos, OpLocalAddr,
				d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
			argDfPtr := currentBlock.NewValue1I(currentBlock.Pos, OpOffPtr, dfBmType.PtrTo(),
				int64(ctrl.ID)*dfBmType.Size(), dfArr)
			ctrlDfs = append(ctrlDfs, currentBlock.NewValue2(currentBlock.Pos, OpLoad, dfBmType, argDfPtr, d.lastMem))
		}

		// Bitwise or two dataflow bitmaps at a time
		for _, ctrlDf := range ctrlDfs {
			currentBlockDf = currentBlock.NewValue2(currentBlock.Pos, OpOr64, dfBmType,
				currentBlockDf, ctrlDf)
		}

		// Store back the dataflow bitmap
		dfArr := currentBlock.NewValue2A(currentBlock.Pos, OpLocalAddr,
			d.blockDfType.PtrTo(), d.blockDfName, d.sp, d.lastMem)
		argDfPtr := currentBlock.NewValue1I(currentBlock.Pos, OpOffPtr, dfBmType.PtrTo(),
			int64(currentBlock.ID)*dfBmType.Size(), dfArr)
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

			if currentVal.Op == OpPhi || currentVal.Op == OpCopy {
				if currentVal.Type.IsMemory() {
					for _, pred := range currentBlock.Preds {
						predBlock := pred.Block()
						currentVal.AddArg(lastMemOfBlock[predBlock])
					}
				} else if currentVal.Type.IsPtr() {
					// Deal with the dfptr of pointers
					if d.isPhiDfPtr[currentVal.ID] {
						continue
					}

					dfPtr := d.ptrToDfPtr[currentVal.ID]
					for _, arg1 := range currentVal.Args {
						// So, we don't need to pass the df for nil ptr
						// It will happen automatically here
						if arg1.Op == OpConstNil {
							d.ptrToDfPtr[currentVal.ID] = d.f.ConstNil(dfBmType.PtrTo())
							break
						}

						argDfPtr := d.ptrToDfPtr[arg1.ID]
						if argDfPtr == nil {
							log.Fatalln("dfptr not found for ptr")
						}
						dfPtr.AddArg(argDfPtr)
					}
				}
			}
		}
	}
}

func (d *dfInstrumentState) onlyPassMem() {
	for vidx := 0; vidx < len(d.initialValues); vidx++ {
		currentVal := d.initialValues[vidx]

		if currentVal.Op == OpArg {
			d.extractDfOfArg(currentVal)

			continue
		}

		if len(currentVal.Args) == 0 {
			continue
		}

		if currentVal.ID <= d.blockDfZeroId {
			continue
		}

		if currentVal.Type.IsMemory() {
			d.resetMem(currentVal)
		}

		// Need to do this to propagate df aross copies and phis
		if currentVal.Op == OpCopy || currentVal.Op == OpPhi {
			d.propagateDfFromArgs(currentVal)
		}
	}
}

// This modifies tha values in the block, a lot
// Should only be called once per block
// Functions used in this should only be called from here
func (d *dfInstrumentState) visitValues() (makeResultValue *Value) {
	for vidx := 0; vidx < len(d.initialValues); vidx++ {
		currentVal := d.initialValues[vidx]

		if currentVal.Op == OpNilCheck ||
			currentVal.Op == OpIsInBounds ||
			currentVal.Op == OpPanicBounds ||
			currentVal.Op == OpAddr {
			continue
		}

		// We added safe_dfptrs to this map
		// Skip if we find them
		if d.isPhiDfPtr[currentVal.ID] {
			continue
		}

		if currentVal.Op == OpArg {
			d.extractDfOfArg(currentVal)

			continue
		}

		// Skip all dataflow array initialization code
		if currentVal.ID <= d.blockDfZeroId {
			continue
		}

		// This like memory init, sp init, args dont need to be tracked
		if len(currentVal.Args) == 0 {
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

			if strings.HasPrefix(auxCall.Fn.Name, "runtime.newobject") {
				_, _ = d.computeDfIndex(currentVal, vidx)
				vidx = d.propagateMemReturn(currentVal, vidx)
				continue
			}

			// For call from dataflow to non dataflow functions
			// TODO: Combine df of all inputs and assign that to dataflow of all outputs
			if !auxCall.Dataflow {
				vidx = d.propagateMemReturn(currentVal, vidx)
				continue
			}

			vidx = d.functionCall(currentVal, vidx)
			continue
		}

		if currentVal.Op == OpSelectN {
			continue
		}

		if currentVal.Op == OpZero {
			d.zeroMem(currentVal)
			continue
		}

		if currentVal.Op == OpMove {
			d.moveMem(currentVal)
			continue
		}

		if currentVal.Op == OpLocalAddr ||
			currentVal.Op == OpOffPtr ||
			currentVal.Op == OpPtrIndex ||
			(currentVal.Op == OpPhi && currentVal.Type.IsPtr()) ||
			(currentVal.Op == OpCopy && currentVal.Type.IsPtr()) {

			// Deal with OpCopy and OpPhi at the end of the block

			// Arg and SelectN of pointers should be evaluated in arg and static call

			// Compute array indices based on this address/pointer instruction
			passDf, _ := d.computeDfIndex(currentVal, -1)
			// Need to pass dataflow for pointer traversal and Phis
			if !passDf {
				continue
			}
		}

		if currentVal.Op == OpLoad || currentVal.Op == OpStore {
			d.loadStore(currentVal)

			continue
		}

		// // Dummy to bypass loadstore instrumentation for testing
		// if currentVal.Op == OpLoad {
		// 	numRealArgs := len(currentVal.Args) - 1
		// 	realArgs := make([]*Value, numRealArgs)
		// 	copy(realArgs, currentVal.Args[:numRealArgs])
		// 	currentVal.resetArgs()
		// 	currentVal.AddArgs(realArgs...)
		// 	currentVal.AddArgs(d.lastMem)

		// 	continue
		// }

		if currentVal.Type.IsMemory() {
			// For example, OpPanicBounds is rewritten here

			d.resetMem(currentVal)
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

	if strings.HasPrefix(argNameStr, "_df_") {
		// Dataflow arg
		// Normal always comes first and the map is populated
		origArgName := strings.Trim(argNameStr, "_df_")
		origArgID := d.argNameStrToDfIdx[origArgName]

		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			origArgID*dfBmType.Size(), dfArr)
		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			argDfPtr, currentVal, d.lastMem)
	} else if strings.HasPrefix(argNameStr, "_dfptr_") {
		// IGNORE: We will deal with it when dealing with Phis
		// Pointer to dataflow
		origArgName := strings.Trim(argNameStr, "_dfptr_")
		origArgID := ID(d.argNameStrToDfIdx[origArgName])

		d.nameToDfPtr[origArgName] = currentVal
		d.ptrToDfPtr[origArgID] = currentVal
	} else if strings.HasPrefix(argNameStr, "_dfblock_") {
		// args, hence blockdf, are always in the first block
		d.currentBlockDf = currentVal
	} else {
		// normal arg
		d.argNameStrToDfIdx[argNameStr] = int64(currentVal.ID)
	}
}

func (d *dfInstrumentState) addDfToReturn(currentVal *Value) (makeResultValue *Value) {
	valPos := currentVal.Pos
	numPrevRealArgs := (len(currentVal.Args) - 2) / 3
	// len-2 because last args are blockdf and memory location
	resDf := make([]*Value, 0, numPrevRealArgs)
	for argidx := 0; argidx < numPrevRealArgs; argidx++ {
		arg1 := currentVal.Args[argidx]

		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			int64(arg1.ID)*dfBmType.Size(), dfArr)
		retvalDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, argDfPtr, d.lastMem)
		combinedDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			d.currentBlockDf, retvalDf)
		resDf = append(resDf, combinedDf)

		if arg1.Type.IsPtr() {
			dfPtr := d.ptrToDfPtr[arg1.ID]
			resDf = append(resDf, dfPtr)
		} else {
			// Return nil ptr for non ptr values
			nilVal := d.f.ConstNil(dfBmType.PtrTo())
			resDf = append(resDf, nilVal)
		}
	}

	prevRealArgs := make([]*Value, numPrevRealArgs)
	copy(prevRealArgs, currentVal.Args[:numPrevRealArgs])
	currentVal.resetArgs()
	currentVal.AddArgs(prevRealArgs...)
	currentVal.AddArgs(resDf...)
	currentVal.AddArgs(d.currentBlockDf)
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
		var markerIdx *Value // Index of bit to set in the bitmap
		for nextVal.Op == OpSelectN {
			if nextVal.Type.IsMemory() {
				d.lastMem = nextVal
			} else if nextVal.AuxInt == 0 {
				// That's the first return value
				markerIdx = nextVal
			}

			retidx++
			nextVal = d.initialValues[vidx+retidx]
		}
		vidx = vidx + retidx - 1

		if markerIdx == nil {
			markerIdx = d.currentBlock.NewValue1I(valPos, OpSelectN, dfBmType,
				0, currentVal)
		}

		dfVal := d.currentBlock.NewValue2(valPos, OpLsh64x64, dfBmType,
			d.f.ConstInt64(dfBmType, int64(1)), markerIdx)

		// Store the dataflow bitmap
		// Set the bitmap for both the passed in argument // and return
		// There were problems with propagation when the argument and return are only
		// operated on by constant values
		arg1 := realArgs[1] // The first arg is a dict, that exists for generic function calls, only when using generics
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			int64(arg1.ID)*dfBmType.Size(), dfArr)
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

		arg1 := realArgs[1] // The first arg is a dict, that exists for generic function calls. Only when using generics
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			int64(arg1.ID)*dfBmType.Size(), dfArr)

		// Basically replace a return with the above load
		retVal.reset(OpLoad)
		retVal.AddArgs(argDfPtr, d.lastMem)
		// retVal.reset(OpCopy)
		// retVal.AddArgs(d.currentBlockDf.Args[0].Args[1])

		return true, vidx
	} else if strings.HasPrefix(auxCall.Fn.Name, "runtime.DfGetArr") ||
		strings.HasPrefix(auxCall.Fn.Name, "runtime.DfGetBlockArr") {

		var heapArr *Value
		var localArr *Value
		var localArrLen int64
		if strings.HasPrefix(auxCall.Fn.Name, "runtime.DfGetArr") {
			heapArr = d.dfArrRetVal
			localArr = d.currentBlock.NewValue2A(valPos, OpLocalAddr,
				d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
			localArrLen = d.dfArrType.NumComponents(true)
		} else if strings.HasPrefix(auxCall.Fn.Name, "runtime.DfGetBlockArr") {
			heapArr = d.blockDfArrRetVal
			localArr = d.currentBlock.NewValue2A(valPos, OpLocalAddr,
				d.blockDfType.PtrTo(), d.blockDfName, d.sp, d.lastMem)
			localArrLen = d.blockDfType.NumComponents(true)
		}

		// Copy df arr into df ret arr
		copyInst := d.currentBlock.NewValue3A(valPos, OpMove, types.TypeMem, d.dfArrType,
			heapArr, localArr, d.lastMem)
		copyInst.AuxInt = d.dfArrType.Size()

		d.lastMem = copyInst

		currentVal.resetArgs()
		currentVal.AddArgs(d.lastMem)

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

		sliceLen := d.f.ConstInt64(types.Types[types.TINT64], localArrLen)
		retVal.reset(OpSliceMake)
		retVal.AddArgs(heapArr, sliceLen, sliceLen)

		return true, vidx
	}

	return false, vidx
}

func (d *dfInstrumentState) propagateMemReturn(currentVal *Value, vidx int) int {
	numRealArgs := len(currentVal.Args) - 1
	realArgs := make([]*Value, numRealArgs)
	copy(realArgs, currentVal.Args[:numRealArgs])
	currentVal.resetArgs()
	currentVal.AddArgs(realArgs...)
	currentVal.AddArgs(d.lastMem)

	retidx := 1
	nextVal := d.initialValues[vidx+retidx]
	for nextVal.Op == OpSelectN {
		if nextVal.Type.IsMemory() {
			// The correct memory location in the return
			// is automatically obtained from func signature
			d.lastMem = nextVal
		}

		retidx++
		nextVal = d.initialValues[vidx+retidx]
	}
	vidx = vidx + retidx - 1

	return vidx
}

func (d *dfInstrumentState) functionCall(currentVal *Value, vidx int) int {
	// No need to change type for this.
	// Type was obtained automatically after
	// func signature modification

	valPos := currentVal.Pos

	numRealArgs := int64(len(currentVal.Args) - 1)
	// len-1 because last arg is memory location
	argDf := make([]*Value, 0, 2*numRealArgs)
	for argidx := int64(0); argidx < numRealArgs; argidx++ {
		arg1 := currentVal.Args[argidx]

		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			int64(arg1.ID)*dfBmType.Size(), dfArr)
		paramDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, argDfPtr, d.lastMem)
		combinedDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			d.currentBlockDf, paramDf)
		argDf = append(argDf, combinedDf)

		if arg1.Type.IsPtr() {
			dfPtr := d.ptrToDfPtr[arg1.ID]
			argDf = append(argDf, dfPtr)
		}
	}

	realArgs := make([]*Value, numRealArgs)
	copy(realArgs, currentVal.Args[:numRealArgs])
	currentVal.resetArgs()
	currentVal.AddArgs(realArgs...)
	currentVal.AddArgs(argDf...)
	currentVal.AddArgs(d.currentBlockDf)
	currentVal.AddArgs(d.lastMem)

	resultsType := currentVal.Type
	numResults := int64(resultsType.NumFields())
	// -2 = -1 for mem, another -1 for block df
	numRealResults := (numResults - 2) / 3

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
			// Need to store based on AuxInt, multiple returns with the same AuxInt
			// have occurred
			realReturnValues[nextVal.AuxInt] = nextVal
		}

		retidx++
		nextVal = d.initialValues[vidx+retidx]
	}
	vidx = vidx + retidx - 1
	// The -1 is necessary as we incremented retidx before breaking out of the above loop

	// Get block df from return [-1 is mem, -2 is blockdf]
	blockDfRet := d.currentBlock.NewValue1I(valPos, OpSelectN, dfBmType,
		numResults-2, currentVal)
	d.currentBlockDf = d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
		d.currentBlockDf, blockDfRet)

	dfValues := make([]*Value, 0, numResults)
	for _, retVal := range realReturnValues {
		if retVal == nil {
			// Actual program did not use this return
			continue
		}

		retvalDfLoc := numRealResults + (2 * retVal.AuxInt)
		retvalDfPtrLoc := retvalDfLoc + 1
		// Use currentVal here as that is the function call
		retvalDf := d.currentBlock.NewValue1I(valPos, OpSelectN, dfBmType,
			retvalDfLoc, currentVal)
		combinedDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			d.currentBlockDf, retvalDf)
		dfValues = append(dfValues, combinedDf)

		if retVal.Type.IsPtr() {
			dfPtr := d.currentBlock.NewValue1I(valPos, OpSelectN, dfBmType.PtrTo(),
				retvalDfPtrLoc, currentVal)
			dfValues = append(dfValues, dfPtr)
		} else {
			dfValues = append(dfValues, nil)
		}
	}

	// After accepting all returns, store the df values to the dataflow array
	for retidx, retVal := range realReturnValues {
		dfVal := dfValues[retidx*2]

		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			int64(retVal.ID)*dfBmType.Size(), dfArr)
		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			argDfPtr, dfVal, d.lastMem)

		if retVal.Type.IsPtr() {
			dfPtr := dfValues[(retidx*2)+1]

			d.ptrToDfPtr[retVal.ID] = dfPtr
		}
	}

	return vidx
}

func (d *dfInstrumentState) zeroMem(currentVal *Value) {
	prevArg1 := currentVal.Args[0]
	// Need to do this as mem value could have changed in the meantime
	currentVal.SetArgs2(prevArg1, d.lastMem)
	d.lastMem = currentVal

	zeroType := currentVal.Aux.(*types.Type)

	if zeroType == nil {
		return
	}

	// Specifically for struct and array types, allocate additional
	// memory for dataflow propagation
	if (zeroType.IsStruct() &&
		!zeroType.IsFuncArgStruct()) ||
		zeroType.IsArray() {

		valPos := currentVal.Pos
		numFields := zeroType.NumComponents(true)
		fullSize := zeroType.Size()
		dfSize := numFields * dfBmType.Size()
		dfStart := fullSize - dfSize

		// Initialize the dataflow values to the current block df
		localAddr := currentVal.Args[0]
		for fidx := int64(0); fidx < numFields; fidx++ {
			dfIdx := dfStart + fidx*dfBmType.Size()
			dfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
				dfIdx, localAddr)
			d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
				dfPtr, d.currentBlockDf, d.lastMem)
		}
	}
}

func (d *dfInstrumentState) moveMem(currentVal *Value) {
	prevArg1 := currentVal.Args[0]
	prevArg2 := currentVal.Args[1]
	// Need to do this as mem value could have changed in the meantime
	currentVal.SetArgs3(prevArg1, prevArg2, d.lastMem)
	d.lastMem = currentVal

	moveType := currentVal.Aux.(*types.Type)

	if moveType == nil {
		return
	}

	if (moveType.IsStruct() &&
		!moveType.IsFuncArgStruct()) ||
		moveType.IsArray() {

		valPos := currentVal.Pos
		numFields := moveType.NumComponents(true)
		fullSize := moveType.Size()
		dfSize := numFields * dfBmType.Size()
		dfStart := fullSize - dfSize

		localAddr := currentVal.Args[0]
		for fidx := int64(0); fidx < numFields; fidx++ {
			dfIdx := dfStart + fidx*dfBmType.Size()
			// load previous df
			dfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
				dfIdx, localAddr)
			// add current block df
			prevDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, dfPtr, d.lastMem)
			newDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType, prevDf, d.currentBlockDf)
			// store back
			d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
				dfPtr, newDf, d.lastMem)
		}
	}
}

func (d *dfInstrumentState) computeDfIndex(currentVal *Value, vidx int) (bool, int) {
	valPos := currentVal.Pos

	if currentVal.Op == OpLocalAddr {
		pointeeType := currentVal.Type.Elem()
		prevArg1 := currentVal.Args[0]
		// Need to do this as mem value could have changed in the meantime
		currentVal.SetArgs2(prevArg1, d.lastMem)

		valName := currentVal.Aux.(*ir.Name)
		valSym := valName.Sym()
		valNameStr := valSym.Name
		dfPtr := d.nameToDfPtr[valNameStr]
		if dfPtr == nil {
			// Only composite types such as structs and arrays have additional metadata
			// Simple types just use the _dataflow_arr
			if currentVal.Type.Elem().IsScalar() {
				dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
					d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
				dfPtr = d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
					int64(currentVal.ID)*dfBmType.Size(), dfArr)
			} else {
				fullSize := pointeeType.Size()
				dfSize := pointeeType.NumComponents(true) * dfBmType.Size()
				dfStart := fullSize - dfSize
				dfPtr = d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
					dfStart, currentVal)
			}
		} else if currentVal.Type.Elem().IsScalar() {
			// Using the previous pointer, but updating lastmem
			dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
				d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
			dfPtr = d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
				dfPtr.AuxInt, dfArr)
		}

		d.nameToDfPtr[valNameStr] = dfPtr
		d.ptrToDfPtr[currentVal.ID] = dfPtr
		return false, vidx
	} else if currentVal.Op == OpCopy || currentVal.Op == OpPhi {
		dfPtr := d.currentBlock.NewValue0(valPos, currentVal.Op, dfBmType.PtrTo())
		d.ptrToDfPtr[currentVal.ID] = dfPtr
		d.isPhiDfPtr[dfPtr.ID] = true
		return true, vidx
	} else if currentVal.Op == OpStaticLECall {
		returnedPtr := d.initialValues[vidx+2]

		pointeeType := returnedPtr.Type.Elem()
		var dfStart int64
		if pointeeType.IsScalar() {
			// Not dealing with 16byte values yet
			dfStart = 8
		} else {
			fullSize := pointeeType.Size()
			// NumComponents returns 1 for scala values. So, no need for scalar check here
			dfSize := pointeeType.NumComponents(true) * dfBmType.Size()
			dfStart = fullSize - dfSize
		}
		dfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			dfStart, returnedPtr)

		d.ptrToDfPtr[returnedPtr.ID] = dfPtr
		return false, vidx + 2
	}

	prevPtr := currentVal.Args[0]
	prevPtrDfPtr := d.ptrToDfPtr[prevPtr.ID]

	var dfPtr *Value
	if currentVal.Op == OpOffPtr { // For struct elements
		// Aux is offset calculated in types/size.go as DfOffset
		staticIndex := auxToInt64(currentVal.Aux)
		dfPtr = d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(), staticIndex, prevPtrDfPtr)
	} else if currentVal.Op == OpPtrIndex { // For array elements
		arrIndex := currentVal.Args[1]
		// Below is basically index in array * number of components of array elem * size of df type
		// dynamicIndex := d.currentBlock.NewValue2(valPos, OpMul32, int32Type, arrIndex, d.f.ConstInt32(int32Type, int32(pointeeType.NumComponents(true))))
		// dynamicIndex = d.currentBlock.NewValue2(valPos, OpMul32, int32Type, dynamicIndex, d.f.ConstInt32(int32Type, int32(dfBmType.Size())))
		dfPtr = d.currentBlock.NewValue2(valPos, OpPtrIndex, dfBmType.PtrTo(), prevPtrDfPtr, arrIndex)
	}

	d.ptrToDfPtr[currentVal.ID] = dfPtr
	return true, vidx
}

func (d *dfInstrumentState) loadStore(currentVal *Value) {
	valPos := currentVal.Pos

	var combinedDf *Value
	var scalarDfPtr *Value
	ptrVal := currentVal.Args[0]

	dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
		d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
	ptrDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
		int64(ptrVal.ID)*dfBmType.Size(), dfArr)
	ptrDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, ptrDfPtr, d.lastMem)

	scalarDfPtr = d.ptrToDfPtr[ptrVal.ID]
	scalarDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, scalarDfPtr, d.lastMem)

	// Combine ptr and embedded field df
	fieldDf := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType, ptrDf, scalarDf)

	// Combine field and block df
	combinedDf = d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
		d.currentBlockDf, fieldDf)

	if currentVal.Op == OpLoad {
		prevArg1 := currentVal.Args[0]
		// Need to do this as mem value could have changed in the meantime
		currentVal.SetArgs2(prevArg1, d.lastMem)

		// In non-optimized build, pointers are loaded before they are used
		if currentVal.Type.IsPtr() {
			d.ptrToDfPtr[currentVal.ID] = d.ptrToDfPtr[prevArg1.ID]
		}

		// Now store the dataflow of the loaded data to the dataflow_arr position of the Load statement
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			int64(currentVal.ID)*dfBmType.Size(), dfArr)
		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			argDfPtr, combinedDf, d.lastMem)
	} else {
		// This can only be OpStore
		// Propagate value from df array to the struct's df space

		prevArg1 := currentVal.Args[0]
		prevArg2 := currentVal.Args[1]
		// Need to do this as mem value could have changed in the meantime
		currentVal.SetArgs3(prevArg1, prevArg2, d.lastMem)

		d.lastMem = currentVal

		dataToStore := currentVal.Args[1]

		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			int64(dataToStore.ID)*dfBmType.Size(), dfArr)
		fieldDf := d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, argDfPtr, d.lastMem)
		combinedDf2 := d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			combinedDf, fieldDf)

		d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
			scalarDfPtr, combinedDf2, d.lastMem)
	}
}

func (d *dfInstrumentState) propagateDfFromArgs(currentVal *Value) {
	valPos := currentVal.Pos

	argsDf := make([]*Value, 0, len(currentVal.Args))
	for _, currentarg := range currentVal.Args {
		if currentarg.Type.IsMemory() {
			// No need to propagate dataflow of memory args
			continue
		}
		dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
			d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
		argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
			int64(currentarg.ID)*dfBmType.Size(), dfArr)
		argsDf = append(argsDf, d.currentBlock.NewValue2(valPos, OpLoad, dfBmType, argDfPtr, d.lastMem))
	}

	// Bitwise or two dataflow bitmaps at a time
	firstArg := d.currentBlockDf
	for _, argDf := range argsDf {
		firstArg = d.currentBlock.NewValue2(valPos, OpOr64, dfBmType,
			firstArg, argDf)
	}

	// Store back the dataflow bitmap
	dfArr := d.currentBlock.NewValue2A(valPos, OpLocalAddr,
		d.dfArrType.PtrTo(), d.dfArrName, d.sp, d.lastMem)
	argDfPtr := d.currentBlock.NewValue1I(valPos, OpOffPtr, dfBmType.PtrTo(),
		int64(currentVal.ID)*dfBmType.Size(), dfArr)
	d.lastMem = d.currentBlock.NewValue3A(valPos, OpStore, types.TypeMem, dfBmType,
		argDfPtr, firstArg, d.lastMem)
}

func (d *dfInstrumentState) resetMem(currentVal *Value) {
	numRealArgs := len(currentVal.Args) - 1
	realArgs := make([]*Value, numRealArgs)
	copy(realArgs, currentVal.Args[:numRealArgs])
	currentVal.resetArgs()
	currentVal.AddArgs(realArgs...)
	currentVal.AddArgs(d.lastMem)

	d.lastMem = currentVal
}

func dataflowInstrument(f *Func) {
	if strings.HasPrefix(f.Name, "DfMark") {
		log.Println("Yippeee!! " + f.Name)
	}

	if !f.Dataflow {
		dfBmType = types.Types[types.TINT64]
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
					argDf := make([]*Value, 0, 2*numRealArgs)
					for argidx := int64(0); argidx < numRealArgs; argidx++ {
						argDf = append(argDf, f.ConstInt64(dfBmType, 0))
						arg1 := currentVal.Args[argidx]
						if arg1.Type.IsPtr() {
							// Using nil here will cause a panic
							// TODO: Send a pointer to empty space instead
							argDf = append(argDf, f.ConstNil(dfBmType.PtrTo()))
						}
					}
					argDf = append(argDf, f.ConstInt64(dfBmType, 0)) // blockdf arg

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
