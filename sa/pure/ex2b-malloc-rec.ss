//include "../../examples/working/cparser/stdhip.h"

data node {
    node next;
}

node malloc_n ()
  requires emp & true ensures res::node<tl>;//'

HeapPred H(node a).
  HeapPred G(node a, node b).


void new_node2 (ref node p)

    infer [H,G] requires H(p) ensures G(p,p'); //'

//  requires p::node<q> & true ensures p'::node<tl> * tl::node<_> & p'=p;//'
{
  p.next = malloc_n();
  p = p.next;
 }
