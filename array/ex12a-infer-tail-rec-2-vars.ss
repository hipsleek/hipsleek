//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
//relation Q(int[] a,int[] b,int r).
relation Q(int a,int b,int r).

  int foo(int a4,int a5,int a6)
 //infer [@arrvar] requires true ensures res=a[5];
//  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
  infer [Q] requires true ensures Q(a4,a5,res);
// requires true ensures update(a,a',10,5) & res=a[4];
// requires true ensures a'[5]=10 & res=a[4];
{
  if (a5>0) {
    a6 = a6+1;
    a5 = a5-1;
    a4 = a4+1;
    return foo(a4,a5,a6); } 
  else return a4;
}

/*
# ex12a.ss 

infer [@arrvar,P,Q,update_array_1d] requires P(a) ensures Q(a,a',res);

# why is there exception despite @arrvar?

!!! **omega.ml#673:WARNING: exception from Omega.is_valid
!!! **omega.ml#673:WARNING: exception from Omega.is_valid

# need to fix fixcalc


Correct RElDEFN:
[RELDEFN Q: ( a'[4]=res & update_array_1d(a,a',10,5) & P(a)) 
     -->  Q(a,a',res)]

# However, it seems we cannot handle update_array_Id subsequently..

ERROR: at _0:0_0:0
Message: compute_def:Error in translating the input for fixcalc
!!! PROBLEM with fix-point calculation
ExceptionFailure("compute_def:Error in translating the input for fixcalc")Occurred!
Error1(s) detected at main 
Stop Omega... 46 invocations caught


[RELDEFN Q: ( 
a'[4]=res & update_array_1d(a,a',10,5) & P(a)) -->  Q(a,a',res)
]


*/
