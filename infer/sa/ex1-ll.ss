data node {
 int val;
 node next;
}

/*
ll<> == self=null 
  or self::node<_,q>*q::ll<>
inv true;
*/

HeapPred H(node x).
HeapPred G(node x, node x).

void trav(ref node x)
 infer [H,G]
 requires H(x)
 ensures  G(x,x');
/*
 requires x::node<_,q>*q::ll<>
 ensures x::node<_,q>*q::ll<>;

 {
  x = x.next;
  if (x!=null) trav(x);
 }
