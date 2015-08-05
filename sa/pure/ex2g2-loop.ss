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

HeapPred H1(node a,node b, int i).
  HeapPred G1( node a, node b,int i, int j,node c, node d).



  void new_node1 (ref int i, ref node t, ref node p)

  infer [H1,G1] requires H1(p,t,i) ensures G1(p,t,i,i',p',t'); //'
//  infer [@shape] requires true ensures true;
/*
  requires p::node<q> * q::lseg<p1> & true
  ensures p::node<p'> * p'::lseg<_>;//'
*/
{
  if (i<10) {
    i++;
    p.h = 1;
    t = malloc_n();
    p.next = t;
    p = p.next;
    new_node1 (i, t, p);
  }
 }



void main()
  infer [@shape] requires true ensures true;
{
  node a = malloc_n();
  node t;
  node p = a;
  int i = 0;
  new_node1(i, t, p);
}
