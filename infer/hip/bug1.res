
Processing file "bug1.ss"
Parsing bug1.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2$int... 
Inferred Heap:[]
Inferred Pure:[ 2<=i]
Residual Post : [ true & i=i'+r_20' & 1<=r_20' & ((0 - i')+2)<=r_20' & r_20'<=2 &
{FLOW,(20,21)=__norm}]

Procedure foo2$int SUCCESS
Stop Omega... 53 invocations 
0 false contexts at: ()

Total verification time: 0.50403 second(s)
	Time spent in main process: 0.384023 second(s)
	Time spent in child processes: 0.120007 second(s)
