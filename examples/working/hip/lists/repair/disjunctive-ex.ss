global int num_a;
global int num_b;

bool foo(int x)
 requires x > 0 ensures res = (num_a > 0) | (num_b < 0);
{
  if (x > 0) return (num_a > 0) || (num_b < 0);
  return true;
}

int test(int x)
requires x > 0 & num_a > 0 & num_b < 0 ensures res = 1;
//requires x <= 0 ensures res = 0;
{
    int alt_sep;
    alt_sep = 0;
    if (foo(x)){
        return 1;
	  }
	  return alt_sep;
}
