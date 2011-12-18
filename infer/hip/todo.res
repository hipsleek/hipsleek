
Processing file "todo.ss"
Parsing todo.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo2$int... 
dprint: todo.ss:12: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:true & 1<i & 1<=r_20' & r_20'<=2 & i'+r_20'=i & {FLOW,(20,21)=__norm}
 ]
Pre Vars :[i]
Exists Post Vars :[r_20']
Residual Post :  true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}
OLD SPECS:  EBase true & 1<i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 1<i & {FLOW,(20,21)=__norm}
         EAssume 1::ref [i]
           true & (i - 2)<=i' & i'<i & 2<=i & {FLOW,(20,21)=__norm}

Procedure foo2$int SUCCESS
Stop Omega... 33 invocations 
0 false contexts at: ()

Total verification time: 0.17 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.01 second(s)
