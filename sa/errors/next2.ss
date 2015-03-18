data node {
  node next;
}

HeapPred H(node a).
HeapPred G(node a, node b).


node get_next(node x)
  infer [H,G]
  requires H(x)   ensures  G(x, res) ;
//  requires x::node<null> ensures x::node<p> & res=p;
{
  return x.next.next;
}

/*
OK
--------
H(x) --> x::node<p1> * HP1(p1) & flow __norm;
HP1<p1> -> p1::node<p2> * HP2<p2>
x::node<p1> * p1::node<p2> * HP2(p2) & res=p2--> G(x,res)

Error
------
H(x) --> x=null; (x=null & flow __Error |- true & flow __Error;)

HP1<p1> --> p1=null; (p1=null & flow __Error |- true & flow __Error;)


 */

/*

H(x) == x::node<p1> * HP1<p1> \/ x=null.

HP1<p1> == p1::node<p2> * HP2<p2> \/ p1 = null.

G(x,res) == x::node<p1> *  p1::node<p2> * HP2<p2> & res=p2.

*/

/*
case {
  x=null -> ensures true & flow __Error;
  x!=null -> requires x::node<p1> * HP1<p1>
    case {
     p1 = null ->  ensures true & flow __Error;
     p1 != null ->  requires x::node<DL2>  ensures G(x,res) & res=DL2;
  }
}

*/
