//include "../../examples/working/cparser/stdhip.h"

//../../hip ex2d-pure-rec.ss --sa-en-pure-field

data node {
  int h;
  node next;
}

lseg<p> ==
  self=p
  or self::node<_,q>*q::lseg<p> 
  inv true;

node malloc_n ()
  requires emp & true ensures res::node<_,tl>;//'

HeapPred H(node a, int i).
  HeapPred G( node a, int i, int j, node d).



  void new_node2 (ref int i, ref node t, ref node p)

  infer [H,G] requires H(p,i) ensures G(p,i,i',p'); //'
//  infer [@shape] requires true ensures true;
/*
  requires p::node<q> * q::lseg<p1> & true
  ensures p::node<p'> * p'::lseg<_>;//'
*/
{
  if (i<10) {
    i++;
    t = malloc_n();
    p.next = t;
    p.h = 1;
    p = p.next;
    new_node2 (i, t, p);
  }
 }

/*
 H(p_1473,i_1474) ::= p_1473::node<h_35_1475,DP_DP_HP_1445>@M&i_1474<10
 or emp&10<=i_1474,
    ^^^ --> htrue



 */
