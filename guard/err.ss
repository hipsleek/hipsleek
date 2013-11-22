data cell {
  int val;
}

HeapPred H(cell a).
HeapPred G(cell a).

int foo(cell p)
  infer [H,G]
  requires H(p)
  ensures G(p);
{
  if (p==null) {
    int i = p.val;
    return i;
  } else return -1;
}
