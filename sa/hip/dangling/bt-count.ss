data node2 {
  int val;
  node2 left;
  node2 right;
}


bst0<> == self = null
	or self::node2<_, p, q> * p::bst0<> * q::bst0<>
	inv true;

HeapPred G1(node2 a).
HeapPred H1(node2 a).

int count(node2 z)
  /*  requires z::bst0<> */
  /* ensures  z::bst0<>; */
  infer[H1,G1]
  requires H1(z)
  ensures G1(z);
{
	int cleft, cright;

	if (z == null)
		return 0;
	else
	{
		cleft = count(z.left);
		cright = count(z.right);
		return (1 + cleft + cright);
	}
}
