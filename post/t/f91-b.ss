// McCarthy 91
// 90 -> 91
relation P(int n, int r).
int f91(int n)
 infer [@term]
 requires true
 ensures res=91 & n<=90 | n=res & res>=91;
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
# f91-b.ss

Can simplify post?
Can simplify Term measure?

f91:  case {
  91<=n -> 
     requires emp & Term[29,1]
     ensures emp & ((res=91 & n<=90) | (n=res & 91<=res)); 
  n<=90 -> 
     requires emp & Term[29,2,90+(-1*n)]
     ensures emp & ((res=91 & n<=90) | (n=res & 91<=res)); 
  }



*/
