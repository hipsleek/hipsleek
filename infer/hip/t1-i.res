
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

OLD SPECS:  EInfer []
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 10::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EAssume 10::ref [i]
   true & true & {FLOW,(20,21)=__norm}

Procedure foo2a$int result FAIL-1
Checking procedure foo2$int... 
Inferred Heap:[]
Inferred Pure:[ 2<=i]
Pre Vars :[i]
Exists Post Vars :[r_24']
Residual Post :  true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}
OLD SPECS:  EInfer [i]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 7::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 2<=i & {FLOW,(20,21)=__norm}
         EAssume 7::ref [i]
           true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}

Procedure foo2$int SUCCESS
Checking procedure foo1a$int... OLD SPECS:  EInfer []
   EBase true & 0<i & {FLOW,(20,21)=__norm}
           EAssume 4::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 4::ref [i]
           true & true & {FLOW,(20,21)=__norm}

Procedure foo1a$int SUCCESS
Checking procedure foo1$int... 
Inferred Heap:[]
Inferred Pure:[ 1<=i]
Pre Vars :[i]
Exists Post Vars :[]
Residual Post :  true & i'+1=i & 1<=i & {FLOW,(20,21)=__norm}
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

Total verification time: 0.25 second(s)
	Time spent in main process: 0.22 second(s)
	Time spent in child processes: 0.03 second(s)
