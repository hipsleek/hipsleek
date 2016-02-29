void error ()
  requires true
  ensures true & flow __Error;

void foo (int n)
  case {
    n >= 0 -> ensures true;
    n < 0 -> ensures true & flow __Error;
  }
{
  if (n == 0) return;
  else if (n < -10) error();
  else foo(n - 1); 
}
