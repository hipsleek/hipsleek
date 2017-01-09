
// 90 -> 91
int f91(int n)
  infer [@post] 
//  requires true ensures true;
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 ->  ensures res=n;
  n<91 -> ensures res=91;
 }
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}

/*
# rec-f91.ss

 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 -> requires Term[] ensures res=n;
  n<91 -> requires Term[91-n] ensures res=91;
 }

Poor result without post. Should the MayLoop conditions be
combined if they have the same post?

Termination Inference Result:
f91:  case {
  n<=90 & n<=89 & n<=0 & n<=(0-1) & n<=(0-2) & n<=(0-
  3) -> requires emp & MayLoop[]
 ensures emp & true; 
  n<=90 & n<=89 & n<=0 & n<=(0-1) & n<=(0-2) & 0<=(2+
  n) -> requires emp & MayLoop[]
 ensures emp & true; 
  n<=90 & n<=89 & n<=0 & n<=(0-1) & 0<=(1+
  n) -> requires emp & MayLoop[]
 ensures emp & true; 
  n<=90 & n<=89 & n<=0 & 
  0<=n -> requires emp & MayLoop[]
 ensures emp & true; 
  n<=90 & n<=89 & 1<=n -> requires emp & MayLoop[]
 ensures emp & true; 
  n<=90 & 90<=n -> requires emp & MayLoop[]
 ensures emp & true; 
  91<=n -> requires emp & Term[29,1]
 ensures emp & true; 

 */
