//specs with explicit errors

int foo1(int x, int y)
 case {
  x = 0 -> ensures true & flow __Error;
  x !=0 -> ensures true;
}
{
  return y/x;
}

int foo2(int x)
 case {
  x = 0 -> ensures res>0 & flow __Error;
  x !=0 -> ensures res=1;
}
{
  if (x==0) return 0;
  else return 1;
}

int foo3(int x)
 case {
  x = 0 -> ensures res>0 & flow __Error;
  x !=0 -> ensures res=1 & flow __Error;
}
{
  if (x==0) return 0;
  else return 1;
}
