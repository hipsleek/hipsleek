data node2 {
  int val;
  node2 left;
  node2 right;
}

bst0<m> == self = null & m = 0
	or self::node2<_, p, q> * p::bst0<m1> * q::bst0<m2> & m = 1 + m1 + m2
	inv m >= 0;

HeapPred G1(node2 a).
HeapPred H1(node2 a).

int count(node2 z)
  /* infer[CNT] */
  /* requires z::bst0<n> */
  /* ensures  z::bst0<n1> & CNT(res,n,n1);//res = n & n>=0 & n=n1; */
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
