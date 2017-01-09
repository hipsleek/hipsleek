int Ack(int m, int n)
  infer [@term]
  case {
    m >= 0 & n >= 0 -> requires true ensures res >= 0;
    !(m >= 0 & n >= 0) -> requires true ensures true;
  }
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
# ack-3.ss

This seems less precise now ..

Termination Inference Result:
Ack:  case {
  m=0 & 0<=n -> requires emp & Term[3,2]
 ensures emp & 0<=res; 
  1<=m & 0<=n -> requires emp & MayLoop[]
 ensures emp & 0<=res; 
  m=0 & n<=(0-1) -> requires emp & Term[3,1]
 ensures emp & true; 
  m<=(0-1) -> requires emp & Loop[]
 ensures false & false; 
  n<=(0-1) & 1<=m -> requires emp & MayLoop[]
 ensures emp & true; 
  }

Ack:  case {
  m=0 & 0<=n -> requires emp & Term[3,2]
 ensures emp & 0<=res; 
  1<=m & 1<=n -> requires emp & Term[3,3,0+(1*m)+(0*n),0+(1*m)+(1*
  n)]
 ensures emp & 0<=res; 
  n=0 & 1<=m -> requires emp & Term[3,3,0+(1*m)+(0*n),0+(1*m)+(1*
  n)]
 ensures emp & 0<=res; 
  m=0 & n<=(0-1) -> requires emp & Term[3,1]
 ensures emp & true; 
  ((n<=(0-1) & 1<=m) | m<=(0-
  1)) -> requires emp & Loop[]
 ensures false & false; 
  }

*/
