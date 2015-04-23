

data node { int val ; node next }


int get_val(node x)
  requires true
  ensures true & flow __norm;
{
  int d = x.val;

  //  dprint;
  return d;
}


int get_val_with_err(node x)
  requires true
  ensures true & flow __Error;
{
  int d = x.val;

  //  dprint;
  return d;
}
