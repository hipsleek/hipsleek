
Processing file "bug1.ss"
Parsing bug1.ss ...
Parsing /home/thaitm/hg-repository/new/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2$int... 
Inferred Heap:[]
Inferred Pure:[ 2<=i]
Pre Vars :[i]
Exists Post Vars :[r_20']
Initial Residual Post : [ true & 1<=r_20' & r_20'<=2 & i'+r_20'=i & 2<=i & {FLOW,(20,21)=__norm}]
Final Residual Post :  true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [i]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 2<=i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}

Procedure foo2$int SUCCESS
Stop Omega... 48 invocations 
0 false contexts at: ()

Total verification time: 0.08 second(s)
	Time spent in main process: 0.06 second(s)
	Time spent in child processes: 0.02 second(s)
