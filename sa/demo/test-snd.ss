data node {
  int val;
  node next;
}


HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node b,node c, node d).

HeapPred H1(node a).

void append(node x)
  infer[H1,G1]  requires H1(x)  ensures G1(x);
{
  assert x!=null;
}
