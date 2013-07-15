data node {
 int val;
 node next;
}

HeapPred H(node x, int v).
PostPred G(node x, int v).

bool check_sorted(node x, int v)
  infer [H,G]
  requires H(x,v) & v>0
  ensures G(x,v) & v=0;
{ 
  dprint;
  return false;
} 

/*
# sorted-1a.ss --en-sleek-logging-txt

GOT
[ H(x,v) --> emp&1>v]

Derived:
[ H(x,v) ::= NONE]
*

==========

Why do we get NONE and not a lhs contradiction formula?

Why did we derive UNKNOWN?

*/