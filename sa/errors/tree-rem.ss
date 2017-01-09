data node {
  int val;
  node left;
  node right;
}

HeapPred H(node a).
  HeapPred G(node a, node b).

  node get_val(node x)
  infer[H,G]
  requires H(x)
     ensures G(x,res);
{
  if (x == null)
    return null;
  else {
    x.left = null;
    return x;
  }
}

/*
case x == null =>
  ensures res = null;
case x != null =>
  requires x::node(val,left,right)
  ensures x::node(val,null,right) & res = x;
*/
