data node {int v}


HeapPred H(node a).
HeapPred G(node a).

  int acc(node x)
//  requires x::node<_> ensures true & flow __Error;
//  requires x::node<_> ensures true ;
//  requires x=null  ensures x=null;
  infer [H,G] requires H(x)   ensures  G(x) ;
/*  infer [@shape,
         @error
         ] requires true   ensures  true ;
*/
{
  x=null;
   dprint;
  return 1;
}
