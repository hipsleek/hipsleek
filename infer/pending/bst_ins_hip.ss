data node3 { 
  int val; 
  node3 left; 
  node3 right; 
}

bst<sm,lg> == self::node3<v,null,null> & sm=v & v=lg 
  or self::node3<v,null,q> * q::bst<qs,lg> & sm=v & v<=qs 
  or self::node3<v,p,null> * p::bst<sm,pl> & sm<=v & v=lg 
  or self::node3<v,p,q> * p::bst<sm,pl> * q::bst<qs,lg> & pl<=v & v<=qs 
  inv sm<=lg;

relation A(int a, int b, int c).

void bst_insert(node3 x, int v)
  infer [A]
  requires x::bst<sm,lg>
  ensures x::bst<mn,mx> & A(mn, mx, v);
{
  node3 p = x.left;
  node3 q = x.right;
  if (v < x.val) {
    if (p == null)
      x.left = new node3(v, null, null);
    else bst_insert(p, v);
  } else {
    if (q == null)
      x.right = new node3(v, null, null);
    else bst_insert(q, v);
  }
}
