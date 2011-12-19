
Processing file "t1-i.ss"
Parsing t1-i.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2a$int... 
procedure call:t1-i.ss:74: 2: 
Verification Context:(Line:65,Col:10)
Proving precondition in method bnd$int for spec:
 EBase true & 0<=i' & {FLOW,(20,21)=__norm}
         EAssume 16::
           true & true & {FLOW,(20,21)=__norm} has failed 

OLD SPECS:  EInfer @post []
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 13::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EAssume 13::ref [i]
   true & true & {FLOW,(20,21)=__norm}

Procedure foo2a$int result FAIL-1
Checking procedure foo2$int... 
Inferred Heap:[]
Inferred Pure:[ 2<=i]
Pre Vars :[i]
Exists Post Vars :[r_25']
Initial Residual Post : [ true & 1<=r_25' & r_25'<=2 & i'+r_25'=i & 2<=i & {FLOW,(20,21)=__norm}]
Final Residual Post :  true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [i]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 10::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 2<=i & {FLOW,(20,21)=__norm}
         EAssume 10::ref [i]
           true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}

Procedure foo2$int SUCCESS
Checking procedure foo1b$int... Pre Vars :[i]
Exists Post Vars :[]
Initial Residual Post : [ true & 0<i & i'+1=i & {FLOW,(20,21)=__norm}]
Final Residual Post :  true & 0<i & i'+1=i & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [i]
   EBase true & 0<i & {FLOW,(20,21)=__norm}
           EAssume 7::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 7::ref [i]
           true & 0<i & i'+1=i & {FLOW,(20,21)=__norm}

Procedure foo1b$int SUCCESS
Checking procedure foo1a$int... Pre Vars :[i]
Exists Post Vars :[]
Initial Residual Post : [ true & 0<i & i'+1=i & {FLOW,(20,21)=__norm}]
Final Residual Post :  true & 0<i & i'+1=i & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer @post []
   EBase true & 0<i & {FLOW,(20,21)=__norm}
           EAssume 4::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 4::ref [i]
           true & 0<i & i'+1=i & {FLOW,(20,21)=__norm}

Procedure foo1a$int SUCCESS
Checking procedure foo1$int... 
Inferred Heap:[]
Inferred Pure:[ 1<=i]
Pre Vars :[i]
Exists Post Vars :[]
Initial Residual Post : [ true & i'+1=i & 1<=i & {FLOW,(20,21)=__norm}]
Final Residual Post :  true & i'+1=i & 1<=i & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [i]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 1<=i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & i'+1=i & 1<=i & {FLOW,(20,21)=__norm}

Procedure foo1$int SUCCESS
Stop Omega... 72 invocations 
0 false contexts at: ()

Total verification time: 0.076003 second(s)
	Time spent in main process: 0.048002 second(s)
	Time spent in child processes: 0.028001 second(s)
