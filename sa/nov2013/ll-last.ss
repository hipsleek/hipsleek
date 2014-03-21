data node {
 int val;
 node next;
}

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x, node v). // non-ptrs are @NI by default

  ll<n:int> == self=null & n=0
  or self::node<v,q>*q::ll<n-1>& self!=null
 inv true;

node last(node x)
  infer [H,G]  requires H(x)  ensures G(x,res);
//  requires true ensures res::ll<m>;
{
  if (x.next == null) return x;
  else return last(x.next);
}
