int Ack(int m, int n)
  infer [@term]
//requires true  ensures res >= n + 1;
  requires true  ensures n>=0 & res>=n+1 | m=0 & n=res-1;
  
{
  if (m == 0) return n + 1;
  else if (n == 0) {
    return Ack(m - 1, 1);
  } else {
    int r = Ack(m, n - 1);
    return Ack(m - 1, r);
  }
}

/*
# ack-5c.ss -infer-lex

this is a stronger post but currently manually
provided

  infer [@term]
//requires true  ensures res >= n + 1;
  requires true  ensures n>=0 | m=0 & n=res-1;

Ack:  case {
  m=0 -> requires emp & Term[3,1]
 ensures emp & (0<=n | (m=0 & n+1=res)); 
  1<=n & 1<=m -> requires emp & Term[3,2,0+(0*m)+(0*n),-1+(1*m)+(0*n),-1+(0*
  m)+(1*n)]
 ensures emp & (0<=n | (m=0 & n+1=res)); 
  m<=(0-1) & 0<=n -> requires emp & Loop[]
 ensures false & false; 
  n=0 & 1<=m -> requires emp & Term[3,2,0+(0*m)+(0*n),-1+(1*m)+(0*n),-1+(0*
  m)+(1*n)]
 ensures emp & (0<=n | (m=0 & n+1=res)); 
  }

*/
