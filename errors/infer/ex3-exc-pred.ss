

int foo(int x)
  requires x>0
  ensures true;

int get_val(int x)
  requires true
  ensures true & flow __norm;
{
  foo(x);

  //  dprint;
  return 0;
}


int get_val_with_err(int x)
  requires true
  ensures true & flow __Error;
{
  foo(x); //should fail immediately as dis-efa-exc

  //  dprint;
  return 0;
}
