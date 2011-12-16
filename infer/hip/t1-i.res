
Processing file "t1-i.ss"
Parsing t1-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2a$int... 
procedure call:t1-i.ss:62: 2: 
Verification Context:(Line:53,Col:10)
Proving precondition in method bnd$int for spec:
 EBase true & 0<=i' & {FLOW,(20,21)=__norm}
         EAssume 13::
           true & true & {FLOW,(20,21)=__norm} has failed 


Procedure foo2a$int result FAIL-1
Checking procedure foo2$int... 
Inferred Heap:[]
Inferred Pure:[ 2<=i]
Residual Post : [ true & i=i'+r_24' & 1<=r_24' & ((0 - i')+2)<=r_24' & r_24'<=2 &
{FLOW,(20,21)=__norm}]

Procedure foo2$int SUCCESS
Checking procedure foo1a$int...  
Residual Post : [ true & 0<i & i'+1=i & {FLOW,(20,21)=__norm}]

Procedure foo1a$int SUCCESS
Checking procedure foo1$int... 
Inferred Heap:[]
Inferred Pure:[ 1<=i]
Residual Post : [ true & i=i'+1 & 0<=i' & {FLOW,(20,21)=__norm}]

Procedure foo1$int SUCCESS
Stop Omega... 83 invocations 
0 false contexts at: ()

Total verification time: 0.98806 second(s)
	Time spent in main process: 0.760046 second(s)
	Time spent in child processes: 0.228014 second(s)
