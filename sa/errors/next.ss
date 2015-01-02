data node {
  node next;
}

HeapPred H(node a).
HeapPred G(node a, node b).


node get_next(node x)
//  requires H(x)   ensures  G(x, res);
//  infer [H,G] requires H(x)   ensures  G(x, res) ;
  infer [@shape
         //@error
         ] requires true   ensures  true ;
///  requires x::node<null> ensures x::node<p> & res=p;
{
  return x.next;
}

/*
# next.ss --sa-error

 H(x3) ::= emp&x3=null(5,9) \/  x3::node<DP>(3,4),
 G(x2,res1) ::= x2::node<res1>&res1=DP(3,4)]


OK
--------
H(x) --> x::node<p> * HP1(p) & flow __norm;
x::node<p> * HP1(p) & res=p --> G(x,res)

Error
------
H(x) --> x=null;

x=null & flow __Error --> true & flow __Error;

 */
