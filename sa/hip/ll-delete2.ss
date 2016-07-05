data node {
	int val;
	node next;
}

ll<> == self=null
	or self::node<_, q> * q::ll<>
	inv true;

node dispose(node x)
  requires x::node<_,_>
  ensures res=null;//'

HeapPred D(node a).
HeapPred E(node a, node b).

void delete_list(ref node x)
  /* infer[D,E] */
  /* requires D(x) */
  /* ensures E(x,x');//' */
  requires x::ll<>
  ensures x=null& x'=null;//'
{
  if (x!=null) {
    delete_list(x.next);
    x= dispose(x);
  }
}
