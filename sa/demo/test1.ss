

data node{
	int val;
	node next;
}

HeapPred H(node a).
HeapPred G(node a).

void foo(node x)
     infer [H,G] requires H(x)ensures G(x);
{
  if (x.next.next != null)
    foo(x.next.next);
}
