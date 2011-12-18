
Processing file "bug1.ss"
Parsing bug1.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2$int... 
Inferred Heap:[]
Inferred Pure:[ 2<=i]
Residual Post : [ true & 1<=r_20' & r_20'<=2 & i'+r_20'=i & 2<=i & {FLOW,(20,21)=__norm}]
Pre Vars :[i]
Exists Post Vars :[r_20']
OLD SPECS:  EInfer [i]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 2<=i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & 1<=r_20' & r_20'<=2 & i'+r_20'=i & 2<=i &
           {FLOW,(20,21)=__norm}

Procedure foo2$int SUCCESS
Stop Omega... 47 invocations 
0 false contexts at: ()

Total verification time: 0.244013 second(s)
	Time spent in main process: 0.132007 second(s)
	Time spent in child processes: 0.112006 second(s)
