void error ()
  requires true
  ensures true & flow __Error;
  
void f (int n)
{
  if (n < 0) error();
  else return;
}

void g(int n)
{
  if (n < 2) g(n + 1);
  else return;
}
