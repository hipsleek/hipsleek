data node {
  int val;
  node next;
}

HeapPred H(node a).
HeapPred G(node a, node b).

HeapPred H1(node a).
HeapPred G1(node a, node b).

node get_last(node x)
  /* infer[H,G] */
  /* requires H(x) */
  /* ensures G(x,res); */
requires true
ensures true;
{
  if (x == null) return null;
  else {
    while (x.next != null)
      infer[H1,G1]
      requires H1(x)
      ensures G1(x,x');
    {
      x = x.next;
    }
    return x;
  }
}
