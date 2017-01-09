int Ack(int m, int n)
 infer [@post_n]
 requires true ensures true;

// requires true
//ensures n>=0 | m=0 & n=res-1;
// ensures res>=n+1;
// ensures n>=0 & res>=n+1 | m=0 & n=res-1;
  
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

Post Inference result:
Ack$int~int
 requires emp & MayLoop[]
 ensures emp & (0<=n | (m=0 & n=res-1));

Can post be made more precise.

Is it possible to infer the more precise:
 (0<=n & res>=n+1 | (m=0 & n=res-1));
or even:
 res>=n+1 ;


*/
