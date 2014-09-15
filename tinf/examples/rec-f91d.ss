
// 90 -> 91
int f91(int n)
  infer [@term] 
  requires true ensures res>=91;
{
  if (91<=n) return n;
  else return f91(f91(n+1));
}

/*
# rec-f91d.ss

Termination Inference Result:
f91:  case {
  n<=90 -> requires emp & Term[29,3,90+(-1*n)]
 ensures emp & 91<=res; 
  91<=n -> requires emp & Term[29,1]
 ensures emp & 91<=res; 
  }

 */
