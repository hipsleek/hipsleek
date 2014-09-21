
!!!Full processing file "examples/sc.ss"
Parsing file "examples/sc.ss" by default parser...

!!! processing primitives "["prelude.ss"]
Starting Omega...oc
Starting z3... 

Checking procedure f$int~int... 
Procedure f$int~int SUCCESS.

Checking procedure f$int~int... 

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
Termination Inference Result:
f:  case {
  x<=0 -> requires emp & Term[29,1]
 ensures emp & true; 
  1<=x -> case {
           0<=y -> requires emp & Loop[]
 ensures false & false; 
           y<=(0-
           1) -> case {
                  1<=x & x<=((0-y)-
                  1) -> requires emp & Term[29,2]
 ensures emp & true; 
                  ((0-x)+1)<=y & y<=(0-
                  1) -> requires emp & Loop[]
 ensures false & false; 
                  y=0-x & 
                  1<=x -> requires emp & Term[29,3]
 ensures emp & true; 
                  }
           
           }
  
  }

0 false contexts at: ()
