data node {
  node next;
}

HeapPred H(node a).
HeapPred G(node a, node b).

node get_next(node x)
  infer [H,G]
  requires H(x)   ensures  G(x, res);
{
  return x.next;
}
