data node {
  node prev;
  node next;
}

HeapPred H(node a).
PostPred G(node a).

void free(node x)
  requires x::node<_,_>
  ensures emp;

void remove(node x)
/*
  infer [H,G]
  requires H(x)
  ensures G(x);
*/
  requires p::node<pp,pn>*x::node<p,n>*n::node<np,nn>
  ensures  p::node<pp,n>*n::node<p,nn>;
  requires x::node<null,n>*n::node<np,nn>
  ensures  n::node<null,nn>;
  requires p::node<pp,pn>*x::node<p,null>
  ensures  p::node<pp,null>;
  requires x::node<null,null>
  ensures  emp;
{
  if (x.prev!=null) 
    x.prev.next = x.next;
  if (x.next!=null) 
    x.next.prev = x.prev;
  free(x);
}
