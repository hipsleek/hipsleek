data node {
 int val;
 node next;
}

HeapPred H(node x, int v).
PostPred G(node x, int v).

bool check_sorted(node x, int v)
  infer [H,G]
  requires H(x,v) & x!=null
  ensures G(x,v) & x=null;
{ 
  dprint;
  return false;
} 

/*
# sorted-1.ss --en-sleek-logging-txt

[ H(x,v) --> emp&x=null]
[ H(x_906,v_907) ::= emp&x_906=null]

==========

Why is the proof log empty? It seems to have
added inferred results but the proof log seems to be
empty. We need to make sure this proof step is
logged.

Why did we derive UNKNOWN?

*/