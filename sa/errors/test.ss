data node {
  int val;
  node next;
}

HeapPred H1(node a).
  HeapPred G1(node a, node b).

  node g(node a)
  infer[H1,G1]
  requires H1(a)
     ensures G1(a,res);
{
  if (a == null)
    {
      return null;
    }
  else if (a.next == null)
    {
      return a;
    }
  else
    {
      return g(a.next);
    }
}

HeapPred H2(node a).
  HeapPred G2(node a, node b).

  node f(node a)
  infer[H2,G2]
  requires H2(a)
     ensures G2(a,res);
{
  return g(a);
}
