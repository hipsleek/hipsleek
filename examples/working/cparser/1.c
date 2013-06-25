struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};

/*@
avl<size, height, S> == self = null & size = 0 & height = 0 & S = {}
  or self::node^<v, height, p, q> * p::avl<size1, height1, S1> * q::avl<size2, height2, S2> & S = union(S1, S2, {v})
  inv size >= 0 & height >= 0;
*/
//  or self::node^<v, height, p, q> * p::avl<size1, height1, S1> * q::avl<size2, height2, S2> & size = 1+size1+size2 & height2<=height1+1 & height1<=height2+1 & height = max(height1, height2) + 1 & S = union(S1, S2, {v})
int find_min(struct node *tree)
/*@
  requires tree::avl<_, _, S> & tree != null
  ensures tree::avl<_, _, S> & tree != null & res in S & forall (a: (a notin S | res <= a));
*/
{
  if (tree->left == NULL)
    return tree->value;
  else
    return find_min(tree->left);
}
