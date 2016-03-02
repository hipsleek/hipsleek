//include "../../examples/working/cparser/stdhip.h"

data node {
    node next;
}

lseg<p> ==
  self=p
  or self::node<q>*q::lseg<p> 
  inv true;

node malloc_n ()
  requires emp & true ensures res::node<tl>;//'

HeapPred H(node a).
  HeapPred G(node a, node b).



  void new_node2 (int i, ref node p)

    infer [H,G] requires H(p) ensures G(p,p'); //'

//  requires p::node<_>  ensures p::lseg<p'>;//'

{
  if (i<0) return;
  else {
    p.next = malloc_n();
    // dprint;
    p = p.next;
    // dprint;
    new_node2 (i, p);
    // dprint;
  }
 }


