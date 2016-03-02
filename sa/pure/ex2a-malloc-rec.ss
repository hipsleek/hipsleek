//include "../../examples/working/cparser/stdhip.h"

data node {
    node next;
}

node malloc_n ()
  requires emp & true ensures res::node<_>;//'

HeapPred H(node a).
  HeapPred G(node a, node b).


void new_node (ref node p)

//   infer [H,G] requires H(p) ensures G(p,p'); //'

  requires emp & true ensures p'::node<_>;//'
{
  p = malloc_n();
 }

