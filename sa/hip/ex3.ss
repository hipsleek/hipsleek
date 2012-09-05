data node {
	int val;
	node next;
}

HeapPred F(node a).

int front(node x)
  infer[F]
  requires F(x)
  ensures true;
{
  return x.val;
}


/*
by hand:
F(x) -> n::node<_,b> * F1(x,b)
auto
 (F(x) --> x::node<_,b> * HP_532(b,x)
//matched
*/

