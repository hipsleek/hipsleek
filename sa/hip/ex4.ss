data node {
	int val;
	node next;
}

void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;

HeapPred D(node a).
void delete_list(ref node x)
  infer[D]
  requires D(x)
  ensures x'=null;
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  }
}
