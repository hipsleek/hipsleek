data node {
	int val;
	node next;
}

HeapPred F(node a).

int front(node x)
  infer[F]
  requires F(x)
  ensures true ;
{
  return x.val;
}

