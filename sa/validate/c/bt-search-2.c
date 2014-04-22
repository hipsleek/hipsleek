struct node2 {
  int val;
  struct node2* left;
  struct node2* right;
};
/*@
bst0<> == self = null
	or self::node2<_, p, q> * p::bst0<> * q::bst0<> & self != null
	inv true;
*/
/*@
HeapPred G1(node2 a).
HeapPred H1(node2 a).
*/
//DFS
  int search(struct node2* x, int a)
  /*@
  infer[H1,G1]
  requires H1(x)
  ensures G1(x);
  */
  /* requires x::bst0<> 
   ensures x::bst0<>;  */
{
  int tmp;
  if (x != NULL)
    {
      // bind x to (xval, xleft, xright) in
      {
        if (x->val == a)
          return 1;
        else {
            if (x->val < a)
              return search(x->right, a);
            else
              return search(x->left, a);
        }
      }
      // return false;
	}
    else return 0;
}
