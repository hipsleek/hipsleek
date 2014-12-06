// McCarthy 91
//f(n,k) = if k <= n then n else f(f(n+1,k),k)
// 90 -> 91
int f91(int n)

  infer [
         @post_n
         //,
         //@term
  ]
  requires true
  ensures true;
/*
 requires true
 ensures n=res & res>=91 | n<91 & res=91;
*/
/*
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 -> requires Term[] ensures res=n;
  n<91 -> requires Term[91-n] ensures res=91;
 }

 requires true
 ensures n=res & res>=91 | n<91 & res=91;

*/
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}
/*
# f91-rec3b.ss

The post-condition generated here is unsound.
It seems some base-case is missing..

RELDEFN post_1319: ( n=res & 91<=res) -->  post_1319(n,res),
RELDEFN post_1319: ( post_1319(v_int_21_1339,res) & n<=90 & post_1319(1+n,v_int_21_1339)) -->  post_1319(n,res)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1319(n,res), n=res & 91<=res, true, true)]
*************************************

!!! REL POST :  post_1319(n,res)
!!! POST:  n=res & 91<=res
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
f91$int
 EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&n=res & 91<=res&{FLOW,(4,5)=__norm#E}[]



# f91-rec3.ss

Qn : Is result below correct? 
 Has the verify of @term been done concurrently 
 with @post, as it will be complex if so.

Post Inference result:
f91$int
 requires emp & f91pre_0(n)[29]
 ensures emp & f91post_1122(n)[] & 
(((res=91 & n<=90) | (n=res & 91<=res)));

Checking procedure f91$int... 

*****************************
*** TERMINATION INFERENCE ***
*****************************
Temporal Assumptions:
 termAssume res=v_int_19_1127' & post_1145(v_int_19_1176,v_int_19_1127') & 
n'<91 & n'=n & !(v_bool_18_1128') & n'<91 & !(v_bool_18_1128') & 
v_int_19_1172=1+n' & 
post_1145(v_int_19_1172,v_int_19_1176) & f91post_1122(v_int_19_1172) & f91post_1122(v_int_19_1176) --> f91post_1122(n).

 termAssume 91<=n' & n'=n & v_bool_18_1128' & 91<=n' & v_bool_18_1128' & 
res=n' --> f91post_1122(n).

 termAssume post_1145(v_int_19_1172,v_int_19_1126') & v_int_19_1172=1+n' & 
!(v_bool_18_1128') & n'<91 & !(v_bool_18_1128') & n'=n & 
n'<91 & f91pre_0(n) --> f91pre_0(v_int_19_1126').

 termAssume n'<91 & n'=n & !(v_bool_18_1128') & n'<91 & !(v_bool_18_1128') & 
v_int_19_1125'=1+n' & f91pre_0(n) --> f91pre_0(v_int_19_1125').


Base/Rec Case Splitting:
[	f91: [[3] 91<=n@B,[4] n<=90@R]
]
Termination Inference Result:
f91:  case {
  91<=n -> requires emp & Term[29,1]
 ensures emp & ((res=91 & n<=90) | 
  (n=res & 91<=res)); 
  n<=90 -> requires emp & MayLoop[]
 ensures emp & ((res=91 & n<=90) | 
  (n=res & 91<=res)); 
  }
Stop Omega... 76 invocations 
0 false contexts at: ()
*/
