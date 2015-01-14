data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, node b).

/* return the last element */
  node prepend(node x, int d)
  infer[H,G]
  requires H(x)
     ensures G(x,res);//'
{
  node new_list = new node(d, null);
  new_list.next = x;

  return new_list;
}
