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
  node tmp = x;
  if (tmp==null) return null;
  else return tmp.next;
}

/* EXPEXTED
case x == null =>
  ensures res = null;
case x != null =>
  requires x::node(val,next)
  ensures x::node(val,next) & res=next;
*/
