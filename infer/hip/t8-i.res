
Processing file "t8-i.ss"
Parsing t8-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo1$int... OLD SPECS:  EInfer [i]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 1<=i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & i'+1=i & 1<=i & {FLOW,(20,21)=__norm}

Procedure foo1$int SUCCESS
Checking procedure foo1a$int... OLD SPECS:  EInfer [i]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 4::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 1<=i & {FLOW,(20,21)=__norm}
         EAssume 4::ref [i]
           true & true & {FLOW,(20,21)=__norm}

Procedure foo1a$int SUCCESS
Checking procedure foo1b$int... OLD SPECS:  EInfer @post []
   EBase true & 0<i & {FLOW,(20,21)=__norm}
           EAssume 7::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 7::ref [i]
           true & 0<i & i'+1=i & {FLOW,(20,21)=__norm}

Procedure foo1b$int SUCCESS
Stop Omega... 57 invocations 
0 false contexts at: ()

Total verification time: 0.376022 second(s)
	Time spent in main process: 0.268016 second(s)
	Time spent in child processes: 0.108006 second(s)
