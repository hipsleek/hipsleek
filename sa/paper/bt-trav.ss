data node2 {
  int val;
  node2 left;
  node2 right;
}

//bst0<> == self = null
//	or self::node2<_, p, q> * p::bst0<> * q::bst0<>
//	inv true;

HeapPred G1(node2 a).
HeapPred H1(node2 a).

//DFS
void trav(node2 x)
  infer[H1,G1]
  requires H1(x)
  ensures G1(x);
  /* requires x::bst0<n>//0<=h & h<=n */
  /* ensures x::bst0<n1>& TRAV(n,n1);//'h1>=0 & n1>=h1 & h1=h & n1=n */
{
  if (x != null){
    /* bind x to (xval, xleft, xright) in */
    {
      //process xval
      trav(x.left);
      trav(x.right);
    }
  }
}
