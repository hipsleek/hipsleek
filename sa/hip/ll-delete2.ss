data node {
	int val;
	node next;
}

node dispose(ref node x)
  requires x::node<_,_>
  ensures res=null;//'

HeapPred D(node a).
HeapPred E(node a, node b).

void delete_list(ref node x)
  infer[D,E]
  requires D(x)
  ensures E(x,x');//'
{
  if (x!=null) {
    delete_list(x.next);
    x= dispose(x);
  }
}
