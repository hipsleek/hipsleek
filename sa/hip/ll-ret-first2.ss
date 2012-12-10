data node {
	int val;
	node next;
}

HeapPred F(node a).
HeapPred G(node a, int r).

int front(node x)
  infer[F,G]
  requires F(x)
  ensures G(x,res);
{
  return x.val;
}

