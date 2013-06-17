data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;


HeapPred H(node a).
HeapPred G(node a).

node foo(node x)
  /* requires x::ll<> & x!=null */
  /* ensures x::ll<> & x!=null & res=x; */
  infer [H,G]
  requires H(x)
  ensures G(x);
{
  if (x.next != null)
    x.next = foo(x.next);

 return x;
}
