//include "../../examples/working/cparser/stdhip.h"

data node {
  int h;
  node next;
}


H_pre<i,p> ==
  p::node<_,q> & i = 0 or p::node<_,q> & i != 0;

node malloc_n ()
  requires emp & true ensures res::node<_,tl>;//'


  void new_node1 (ref int i, ref node t, ref node p)

  //  requires p::node<_,q> & i = 0 or p::node<_,q> & i != 0
   requires t::H_pre<i,p>
  ensures true;

{
  if (i==0) {
    p.h = 1;
    t = malloc_n();
    p.next = t;
    p = p.next;
    i=1;
  }
  else {
    p.h = 2;
    t = malloc_n();
    p.next = t;
    p = p.next;
    i=0;
  }
   new_node1 (i, t, p);
 }



void main()
  infer [@shape] requires true ensures true;
{
  node a = malloc_n();
  node t;
  node p = a;
  int i = 0;
  dprint;
  new_node1(i, t, p);
}
