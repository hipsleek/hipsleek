//specs with explicit errors

int foo(int x, int y)
 case {
  x = 0 -> ensures true & flow __Error;
  x !=0 -> ensures true;
}
{
  return y/x;
}
