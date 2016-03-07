relation P2(int n).

void error ()
  requires true
  ensures true & flow __Error;
  
bool nondet ()
  requires true
  ensures true;

void foo (int n)
  //requires n<0
  //ensures true & flow __Error;
  
  infer[P2]
  requires P2(n)
  ensures true & flow __Error;
  
{
  if (n == 0) return;
  else if (nondet()) foo(n - 1);
  else error(); 
}
