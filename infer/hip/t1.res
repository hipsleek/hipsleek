
Processing file "t1.ss"
Parsing t1.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2$int... OLD SPECS:  EBase true & 1<i & {FLOW,(20,21)=__norm}
         EAssume 4::ref [i]
           true & i<=(i'+2) & (i'+1)<=i & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 1<i & {FLOW,(20,21)=__norm}
         EAssume 4::ref [i]
           true & i<=(i'+2) & (i'+1)<=i & {FLOW,(20,21)=__norm}

Procedure foo2$int SUCCESS
Checking procedure foo1$int... OLD SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & i'+1=i & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & i'+1=i & {FLOW,(20,21)=__norm}

Procedure foo1$int SUCCESS
Stop Omega... 39 invocations 
0 false contexts at: ()

Total verification time: 0.2 second(s)
	Time spent in main process: 0.18 second(s)
	Time spent in child processes: 0.02 second(s)
