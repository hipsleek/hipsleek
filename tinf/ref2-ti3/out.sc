
!!!Full processing file "examples/sc.ss"
Parsing file "examples/sc.ss" by default parser...

!!! processing primitives "["prelude.ss"]
Starting Omega...oc
Starting z3... 

Checking procedure f$int~int... 
Procedure f$int~int SUCCESS.


*****************************
*** TERMINATION INFERENCE ***
*****************************
Temporal Assumptions:
 termAssume v_int_23_1186=y'+x' & v_int_23_1185=y'+x' & !(v_bool_22_1127') & 
0<x' & !(v_bool_22_1127') & x'=x & y'=y & 
0<x' & fpost_1123(v_int_23_1185,v_int_23_1186) --> fpost_1123(x,y).

 termAssume x'<=0 & y'=y & x'=x & v_bool_22_1127' & x'<=0 & 
v_bool_22_1127' --> fpost_1123(x,y).

 termAssume 0<x' & y'=y & x'=x & !(v_bool_22_1127') & 0<x' & 
!(v_bool_22_1127') & v_int_23_1126'=y'+x' & v_int_23_1125'=y'+
x' & fpre_0(x,y) --> fpre_0(v_int_23_1126',v_int_23_1125').


Base/Rec Case Splitting:
[	f: [[2] x<=0@B,[3] 1<=x@R]
]

Context of Verification Failure: 1 File "examples/sc.ss",Line:7,Col:10
Last Proving Location: 1 File "examples/sc.ss",Line:23,Col:7

ERROR: at _0:0_0:0 
Message: [TNT Inference]: One of analyzed scc's successors is Unknown.
 Termination Inference Result:
f:  case {
  x<=0 -> requires emp & Term[29,1]
 ensures emp & true; 
  1<=x -> requires emp & MayLoop[]
 ensures emp & true; 
  }
Stop Omega... 23 invocations 
0 false contexts at: ()

!!! log(small):(0.038254,226)
Total verification time: 0.33429 second(s)
	Time spent in main process: 0.314265 second(s)
	Time spent in child processes: 0.020025 second(s)

