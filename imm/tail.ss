data node{
	int val;
	node next;
}

HeapPred H1(node a).
HeapPred G1(node a, node b).

node foo (node c)
  infer [ann1,ann2]
  requires c::node<a,b>@ann1
  ensures c::node<a,b>@ann2 & res=b;

/*
  infer[H1,G1] 
  requires H1(c) 
  ensures G1(res,c);
*/
{
    return c.next;
}

