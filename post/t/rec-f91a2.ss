
// 90 -> 91
relation postA(int n, int r).
relation postB(int n, int r).

int f91(int n)
  infer[@term]
 case {
  n>=91 ->  ensures n=res;
  n<91 -> ensures res=91;
 }
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}

/*
# rec-f91a2.ss

  infer[@term]
 case {
  n>=91 ->  ensures n=res;
  n<91 -> ensuresres=91;
 }

Why @term succeed here but not in rec-f91.ss?

Termination Inference Result:
f91:  case {
  91<=n -> requires emp & Term[30,1]
     ensures emp & 91<=n & n=res; 
  n<=90 -> requires emp & Term[30,2,90+(-1*n)]
     ensures emp & n<91 & 
  res=91; 
  }


*/
