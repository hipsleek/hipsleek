data node {
  int val;
  node left;
  node right;
}

HeapPred H(node a).
  HeapPred G(node a, int v).

  int get_val(node x)
  infer[H,G]
  requires H(x)
     ensures G(x,res);
{
  if (x == null)
    return 0;
  else
    return x.val;
}

/*
case x == null =>
  ensures res = 0;
case x != null =>
  requires x::node(val,left,right)
  ensures x::node(val,left,right) & res = val;
*/
