
Processing file "t1.ss"
Parsing t1.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2$int... Pre Vars :[i]
Exists Post Vars :[r_21']
Residual Post :  true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}
OLD SPECS:  EBase true & 1<i & {FLOW,(20,21)=__norm}
         EAssume 4::ref [i]
           true & i<=(i'+2) & (i'+1)<=i & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 1<i & {FLOW,(20,21)=__norm}
         EAssume 4::ref [i]
           true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}

Procedure foo2$int SUCCESS
Checking procedure foo1$int... Pre Vars :[i]
Exists Post Vars :[]
Residual Post :  true & 0<i & i'+1=i & i'+1=i & {FLOW,(20,21)=__norm}
OLD SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & i'+1=i & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & 0<i & i'+1=i & i'+1=i & {FLOW,(20,21)=__norm}

Procedure foo1$int SUCCESS
Stop Omega... 40 invocations 
0 false contexts at: ()

Total verification time: 0.420024 second(s)
	Time spent in main process: 0.33602 second(s)
	Time spent in child processes: 0.084004 second(s)
