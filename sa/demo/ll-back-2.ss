data node {
  node next;
}

ll1<> == self::node<q> * q::ll1<>
  inv true;

ll<> == self = null
	or self::node<q> * q::ll<>
  inv true;

HeapPred H1(node a).
HeapPred G2(node b, node c).
HeapPred G1(node b).

node malloc(int s)
  requires true
  ensures res::node<_> or res=null;

node build (int n)
/*
 requires true
 ensures res::ll<>;
*/
 infer [G1]
 requires true
 ensures G1(res);
{
  if (n==0) return null;
  else {
     return new node(build(n-1));
  } 
}
