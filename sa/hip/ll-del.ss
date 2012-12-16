data node {
  int val;
  node next;
}

HeapPred G2(node a, node b).
HeapPred H1(node a).

node delete(node x, int a)
  /* requires x::ll1<> & a > 0 */
  /* ensures x::ll1<>; */

//G1 can not be a lseg because y!=null
  infer[H1,G2]
  requires H1(x)
     ensures G2(x,res) ;


{
  	if (x == null)
		return x;
	else
  {
		if (x.val == a)
      return x.next;
		else
      return new node(x.val, delete(x.next, a));
  }
}
