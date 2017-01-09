data node {int v}


HeapPred H(node a).
HeapPred G(node a).

  node free(node x)
 case {
  x!=null ->
  requires x::node<_> ensures emp;
  x=null ->  ensures true & flow __Error;
}

int double_free(node x)
  requires x::node<_> ensures true & flow __Error;
//  infer [H,G] requires H(x)   ensures  G(x) ;
/*  infer [@shape,
         @error
         ] requires true   ensures  true ;
*/
{
  free(x);
  free(x);
  return 0;
}
