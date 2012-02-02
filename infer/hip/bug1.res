
Processing file "bug1.ss"
Parsing bug1.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2$int... 
Inferred Heap:[]
Inferred Pure:[ 2<=i]
OLD SPECS:  EInfer [i]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 2<=i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}
NEW RELS: []

Procedure foo2$int SUCCESS
Stop Omega... 45 invocations 
0 false contexts at: ()

Total verification time: 0.14 second(s)
	Time spent in main process: 0.13 second(s)
	Time spent in child processes: 0.01 second(s)
