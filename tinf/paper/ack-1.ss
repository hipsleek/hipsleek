//template int r(int m, int n).

//template int r1(int m, int n).
//template int r2(int m, int n).

int Ack(int m, int n)
  //infer[@term]
  //requires true
  //ensures (!(m >= 0 & n >= 0) | res >= 0);
  /*
  infer [r]
  //requires m >= 0 & n >= 0 & Term[r(m, n)]
  //ensures res >= 0;
  requires m >= 0 & n >= 0
  case {
    m = 0 -> requires Term ensures res >= 0;
    m != 0 -> requires Term[r(m, n)] ensures res >= 0;
  }
  */
  /*
  infer [r1, r2]
  //infer [r]
  requires m >= 0 & n >= 0
  case {
    m = 0 -> requires Term ensures res >= 0;
    m != 0 -> case {
      n != 0 -> requires Term[r1(m, n)] ensures res >= 0;
      n = 0 -> requires Term[r2(m, n)] ensures res >= 0;
    }
  }
  */
  
  infer [@term]
  requires m >= 0 & n >= 0
  case {
    m = 0 -> requires Term ensures res >= 0;
    m != 0 -> requires true ensures res >= 0;
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
# ack-1.ss

Ack:  requires emp & 0<=m & 0<=n
case {
     m=0 -> 
       requires emp & Term[3]
       ensures emp & 0<=res; 
     (1<=m | m<=(0-1)) -> case {
             m=0 & 0<=n -> 
               requires false & false
               ensures false & false; 
             1<=n & 1<=m -> 
               requires emp & Term[3,2,0+(1*m)+(0*n),0+(1*m)+(1n)]
               ensures emp & 0<=res; 
             n=0 & 1<=m -> 
               requires emp & Term[3,2,0+(1*m)+(0*n),0+(1*m)+(1*n)]
               ensures emp & 0<=res; 
             }

 */
