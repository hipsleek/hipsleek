relation P2(int n).

void error ()
  requires true
  ensures true & flow __Error;

void foo (int n)
  infer [P2]
  requires P2(n) & n>=0
  ensures true & flow __Error;
  
  //(1)
  //requires P2(n)
  //ensures false;
  
  //(2)
  //requires P2(n) & n+5>=0
  //ensures true & flow __Error;
  
  //(3)
  requires P2(n) & n+5>=0 & !(n<0)
  ensures true;
{
  if (n == 0) return;
  else foo(n - 1); 
}
