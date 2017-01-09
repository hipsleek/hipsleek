// McCarthy 91
// 90 -> 91
relation P(int n, int r).
int f91(int n)
  infer [
         //@post_n,
         @term
 ]
 requires true
  ensures true; //(((res=91 & n<=90) | (n=res & 91<=res)));
  //  n>91 -> requires Term[] ensures res=n;
/*
 case {
  n>=91 -> ensures res=n;
  n<91 -> ensures res=91;
 }
*/
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}

/*
# f91-z.ss [@term,@post_n]

Can re-verify be done at the end after all
inferences?

Post Inference result:
f91$int
 requires emp & f91pre_0(n)[29]
 ensures emp & f91post_1124(n)[] & 
(((res=91 & n<=90) | (n=res & 91<=res)));

Checking procedure f91$int... 
!!! Performing a Re-verification, Valid?:true

Base/Rec Case Splitting:
[	f91: [[3] 91<=n@B,[4] n<=90@R]
]
Termination Inference Result:
f91:  case {
  91<=n -> requires emp & Term[29,1]
 ensures emp & ((res=91 & n<=90) | 
  (n=res & 91<=res)); 
  n<=90 -> requires emp & Term[29,2,90+(-1*n)]
 ensures emp & ((res=91 & 
  n<=90) | (n=res & 91<=res)); 
  }

*/
