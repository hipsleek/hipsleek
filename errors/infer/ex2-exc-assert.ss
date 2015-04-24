

data node { int val ; node next }

/*
int get_val(node x)
  requires true
  ensures true & flow __norm;
{
  assert (x'!=null) assume true;
  return 0;
}
*/


int get_val_with_err(node x)
  requires true
  ensures true & flow __Error;
{
   assert (x'!=null) ; //assume true;
    dprint;
  return 0;
}

