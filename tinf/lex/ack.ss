int Ack(int m, int n)
  //infer [@term]
  //requires true
  //ensures res >= n + 1;
  //ensures true;
  
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
# ack-5.ss -infer-lex

very nice example!

Ack:  case {
  m=0 -> 
    requires emp & Term[3,1]
    ensures emp & (1+n)<=res; 
  1<=n & 1<=m -> 
    requires emp & Term[3,2,-1+(1*m)+(0*n),-2+(1*m)+(1*n)]
    ensures emp & (1+n)<=res; 
  ((m<=(0-1) & n<=(0-1)) | (n<=(0-1) & 1<=m) | (m<=(0-1) & 
  0<=n)) -> 
    requires emp & Loop[]
    ensures false & false; 
  n=0 & 1<=m -> 
    requires emp & Term[3,2,-1+(1*m)+(0*n),-2+(1*m)+(1*n)]
    ensures emp & (1+n)<=res; 
  }
*/
