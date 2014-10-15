/* bst trees */
/* representation of a node in an bst tree */
data node {
	int val;
	node left;
	node right;
}

/* view for bst trees */
bst<S> == self = null & S = {}
  or  self::node<v,p,q> * p::bst<S1> * q::bst<S2> & S = union(S1, S2, {v}) &
       forall(x: (x notin S1 | v >= x)) &
       forall(y: (y notin S2 | v < y));


node search(node x, int k)
  	requires x::bst<S> & k in S
  ensures true;//res::node<k, _, _> ;
{
  if (x == null) return x;
  if (x.val == k){
    return x;
  }
  else if (x.val < k){
   return search (x.left, k);
  }
  else{
    return search (x.right, k);
  }
}
