int Ack(int m, int n)
  infer [@term]
  requires true
  ensures (!(m >= 0 & n >= 0) | res >= 0);
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
# ack-2.ss

  infer [@term]
  requires true
  ensures (!(m >= 0 & n >= 0) | res >= 0);

This seems to be going into a Loop..

Ack:  case {
  m=0 -> 
   requires emp & Term[3,1]
   ensures emp & (!((0<=m & 0<=n)) | 0<=res); 
  1<=m & 1<=n -> 
   requires emp & Term[3,2,-1+(1*m)+(0*n),-2+(1*m)+(1*n)]
   ensures emp & (!((0<=m & 0<=n)) | 0<=res); 
  ((m<=(0-1) & n<=(0-1)) | (n<=(0-1) & 1<=m) | (m<=(0-1) & 
  0<=n)) -> 
    requires emp & Loop[]
    ensures false & false; 
  n=0 & 1<=m -> 
    requires emp & Term[3,2,-1+(1*m)+(0*n),-2+(1*m)+(1*n)]
    ensures emp & (!((0<=m & 0<=n)) | 0<=res); 
  }
 */
