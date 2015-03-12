data node{
  int val;
  node next;
}

HeapPred P(node x).
  PostPred Q(node x,node y).

node tail_fn(node x)
  infer [P,Q]
  requires P(x)
  ensures Q(x,res);
{
  return x.next;
}
