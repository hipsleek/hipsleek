relation P(int x, int y).

int mc(int n) 
 infer [P]
 requires true
  ensures P(n,res);
{
  if (n>100) return n-10;
    else return mc(mc(n+12));
}
