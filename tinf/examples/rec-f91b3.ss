// McCarthy 91
//f(n,k) = if k <= n then n else f(f(n+1,k),k)
/*
int f(int n, int k)
//if spec below used, term error occurs.
//requires true
//ensures true;
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=k -> requires Term[] ensures res=n;
  n<k -> requires Term[k-n] ensures res=k;
}
{
  if (k<=n) return n;
  else return f(f(n+1,k),k);
}
*/

// 90 -> 91
int f91(int n)
  infer [@term] 
 requires true ensures true;
/*
 case {
  //  n>91 -> requires Term[] ensures res=n;
  n>=91 -> requires Term[] ensures res=n;
  n<91 -> requires Term[91-n] ensures res=91;
 }
*/
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}

/*

# rec-f91b3.ss

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
