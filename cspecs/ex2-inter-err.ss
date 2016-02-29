void error ()
  requires true
  ensures true & flow __Error;
  
void f (int n)
  case {
    n >= 0 -> ensures true;
    n < 0 -> ensures true & flow __Error;
  }
{
  if (n < 0) error();
  else return;
}

void g(int n)
  case {
    n >= 2 -> ensures true;
    n < 2 -> case {
      n >= -1 -> ensures true;
      n < -1 -> ensures true & flow __Error;
    } 
  }
{
  if (n < 2) f(n + 1);
  else return;
}
