data node{
  int val;
  node next;
}

HeapPred P(node x,node y).
PostPred Q(node x,node y).

void set_tail_fn(node x,node y)
  infer [P,Q]  requires P(x,y) ensures Q(x,y);
{ 
  x.next=y;
}
