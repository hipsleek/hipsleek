 data node {
  int val;
  node  next;
}


HeapPred H( node a).
HeapPred G( node a).


int main(node l)
{

  int i=0;

  while (l !=null)
    infer [H,G]
      requires H(l)
      ensures G(l');//'
    {
      l = l.next;
      i++;
  }

  return i;
}
