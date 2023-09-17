# Breadcrumbs - Dynamic Dataflow Analysis for Go

Breadcrumbs adds an additional feature to the go compiler which allows the user to track which inputs the program influence which outputs.

Breadcrumbs extends go version 1.20.5. Mark functions which you want use breadcrumbs on with the `//go:dataflow` compiler directive to enable dataflow analysis for that function.

### Compiling breadcrumbs
All documentation for compiling and developing the standard go compiler applies to breadcrumbs. Run `./make.bash` in the src folder to compile the linux version. The binaries will appear in the bin directory.

### Usage notes
Dataflow analysis requires `sources` and `sinks` to work. Data source can be marked using the `runtime.DfMark(variableToMark any) int` function. It returns an integer which specifies the index of the source in the dataflow bitmap. Store this to later analyze the sinks.

The dataflow bitmap of a variable can be obtained using the `runtime.DfInspect(variable any) int64` function. The return value is the dataflow bitmap.

A maximum of 63 dataflows can be tracked in a single run. To track more, run the same code multiple times with different variables marked.

### Developing breadcrumbs
Most of the breadcrumbs code lives in `src/cmd/compile/internal/dataflow/dataflow.go` and `src/cmd/compile/internal/ssa/dataflow_instrument.go`. Additional space for dataflow is allocated in the `runtime.newobject` function and in `src/cmd/compile/internal/types/size.go`.

To debug a function dataflow, use `GOSSAFUNC=functionname` along with the usual go commands to dump the SSA of the function with and without dataflow instrumentation. Use the runtime functions `runtime.GetDfArr() []int64` and `runtime.GetBlockDfArr() int64` to obtain slices which represent the dataflow array and control-flow based dataflow arrays for a specific function.

### Work in Progress
Not all language features are supported. The project is under development.
