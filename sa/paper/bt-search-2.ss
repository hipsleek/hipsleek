data node2 {
  int val;
  node2 left;
  node2 right;
}

bst0<> == self = null
	or self::node2<_, p, q> * p::bst0<> * q::bst0<>
	inv true;

bst1<> == self = null
	or self::node2<_, p, q> * p::bst0<> * q::bst0<>
        or self::node2<_, p, q> * p::bst0<> * q::bst1<>
	inv true;

bst2<mi,ma> == self=null
  or self::node2<v, l, r> * l::bst2<mi,v> * r::bst2<v,ma> & v>mi & v<=ma;

HeapPred G1(node2 a).
HeapPred H1(node2 a).
  HeapPred H1(node2 a, int b).

//DFS
  bool search(node2 x, int a)
  //infer[H1,G1]  requires H1(x, a)  ensures G1(x);
  requires x::bst2<mi,ma> & a>mi & a<=ma & x!=null
  ensures res;
  /* requires x::bst0<> */
  /* ensures x::bst0<> & (res | !res);//'n>=0 & h>=0 & n=n1 & h=h1 */
{
  	int tmp;

	if (x != null)
	{
      // bind x to (xval, xleft, xright) in
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
      // return false;
	}
    else return false;
}
