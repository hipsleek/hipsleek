relation P2(int n).

void error ()
  requires true
  ensures true & flow __Error;

void foo (int n)
  infer [P2]
  requires P2(n)
  ensures true & flow __Error;
{
  if (n == 0) return;
  else error();
}
