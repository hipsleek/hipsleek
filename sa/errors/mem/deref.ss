data node {int v}


HeapPred H(node a).
HeapPred G(node a).

int acc(node x)
//  requires true ensures true & flow __Error;
//  infer [H,G] requires H(x)   ensures  G(x) ;
  infer [@shape,
         @error
         ] requires true   ensures  true ;
{
  return x.v;
}
