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



  void new_node2 (ref int i, ref node p)

    infer [H,G] requires H(p) ensures G(p,p'); //'
/*
  requires p::node<q> * q::lseg<p1> & true
  ensures p::node<p'> * p'::lseg<_>;//'
*/
{
  if (i<10) {
    i++;
    p.next = malloc_n();
    p = p.next;
    new_node2 (i, p);
  }
 }
