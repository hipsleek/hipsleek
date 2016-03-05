relation P2(int n).

void error ()
  requires true
  ensures true & flow __Error;

void foo (int n)
  infer [P2]
  
  //(1)
  //requires P2(n)
  //ensures false;
  
  //(2)
  //requires P2(n) & n>=0
  //ensures true & flow __Error;
  requires P2(n)
  ensures n>=0 & flow __Error;
{
  if (n == 0) return;
  else foo(n - 1); 
}
