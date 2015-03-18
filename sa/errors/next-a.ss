data node {
  node next;
}

HeapPred H(node a).
HeapPred G(node a, node b).



node get_next(node x)
  infer [H,G]
  requires H(x)   ensures  G(x, res) ;
//  requires x::node<p> or x=null ensures x::node<p> & res=p or x=null & res=null;
{
  if (x == null) return null;
  else
    return x.next;
}

/*
OK
--------
H(x) --> x::node<p> * HP1(p) & flow __norm;
x::node<p> * HP1(p) & res=p --> G(x,res)

Error
------
H(x) --> x=null;

x=null & flow __Error --> true & flow __Error;

 */
