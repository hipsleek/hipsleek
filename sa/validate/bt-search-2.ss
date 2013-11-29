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

//DFS
  bool search(node2 x, int a)
  infer[H1,G1]
  requires H1(x)
  ensures G1(x);

  /* requires x::bst0<> */
  /* ensures x::bst0<> & (res | !res);//'n>=0 & h>=0 & n=n1 & h=h1 */
{
  int tmp;

  if (x != null)
    {
      if (x.val == a)
        return true;
      else {
        if (x.val < a)
          return search(x.right, a);
        else
          return search(x.left, a);
      }
    }
  else return false;
}
