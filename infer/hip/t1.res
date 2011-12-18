
Processing file "t1.ss"
Parsing t1.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2$int... Residual Post : [ true & 1<i & 1<=r_21' & r_21'<=2 & i'+r_21'=i & {FLOW,(20,21)=__norm}]
Pre Vars :[i]
Exists Post Vars :[r_21']
OLD SPECS:  EBase true & 1<i & {FLOW,(20,21)=__norm}
         EAssume 4::ref [i]
           true & i<=(i'+2) & (i'+1)<=i & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 1<i & {FLOW,(20,21)=__norm}
         EAssume 4::ref [i]
           true & 1<i & 1<=r_21' & r_21'<=2 & i'+r_21'=i & i<=(i'+2) & (i'+
           1)<=i & {FLOW,(20,21)=__norm}

Procedure foo2$int SUCCESS
Checking procedure foo1$int... Residual Post : [ true & 0<i & i'+1=i & {FLOW,(20,21)=__norm}]
Pre Vars :[i]
Exists Post Vars :[]
OLD SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & i'+1=i & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 0<i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & 0<i & i'+1=i & i'+1=i & {FLOW,(20,21)=__norm}

Procedure foo1$int SUCCESS
Stop Omega... 39 invocations 
0 false contexts at: ()

Total verification time: 0.236013 second(s)
	Time spent in main process: 0.140008 second(s)
	Time spent in child processes: 0.096005 second(s)
