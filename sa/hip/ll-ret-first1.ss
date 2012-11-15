data node {
	int val;
	node next;
}

HeapPred H1(node a).
  HeapPred G2(node a,node b).

node ret_first(node x)
  infer[H1,G2]
  requires H1(x)
  ensures G2(x,res);
{
  return x;
}



