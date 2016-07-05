data node {
  int val;
  node next;
}

ll<> == self=null
	or self::node<_, q> * q::ll<> & self!=null
	inv true;

HeapPred H(node a).
  HeapPred G(node a, node b).

/* return the last element */
  node prepend(node x, int d)

  infer[H,G]
  requires H(x)
     ensures G(x,res);//'

/*
 requires true
 ensures res::node<_,x>;
*/
{
  node new_list = new node(d, null);
  new_list.next = x;

  return new_list;
}


node testhar(node x)
  requires x::ll<>@I
  ensures res::node<_,x>;
{
  return prepend(x,0);
}
