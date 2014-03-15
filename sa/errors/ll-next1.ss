data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, node b).
 
/* return the tail of a singly linked list */
  node get_next(node x)
  infer[H,G]
  requires H(x)
     ensures G(x,res);//'
{
  if (x==null) return null;
  else if (x.next == null) return new node(0,null);
  else {
    x.val = 1;
    return x;
  }
}

/*
case x == null =>
  ensures res = null;
case x != null =>
  requires x::node(val,next)
  ensures x::node(val,res);
*/
