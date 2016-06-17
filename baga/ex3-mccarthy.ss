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
       emp&((n>=101 & n=res+10) | (100>=n & 91=res))&{FLOW,(4,5)=__norm#E}[]
*/
