relation P(int x, int y).

int mc(int n) 
 infer [P]
 requires true
  ensures P(n,res);
{
  if (n>100) return n-10;
    else return mc(mc(n+11));
}

/*
     EAssume 
       emp&((res>=91 & res+10=n) | (res>=91 & (res+8)>=n & 92>=res))&
*/
