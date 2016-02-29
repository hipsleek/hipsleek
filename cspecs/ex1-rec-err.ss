void error ()
  requires true
  ensures true & flow __Error;

void foo (int n)
{
  if (n == 0) return;
  else if (n < 10) error();
  else foo(n - 1); 
}
