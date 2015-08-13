/* Build a list of the form 1->...->1->0 */

data node {
 int h;
 node next;
}

bool bool_nondet()
  requires emp & true ensures emp & true;

node new_node()
  requires emp & true ensures res::node<_,_>;

//HeapPred H(node x, node b). // non-ptrs are @NI by default
//  PostPred G(node x,  node b,  node c, node d). // non-ptrs are @NI by default

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x,  node b).

ll_one<> == self=null
  or self::node<1,q>*q::ll_one<>
  ;

lseg_one<p> == self=p
  or self::node<1,q>*q::lseg_one<p>
  ;


void create_one (ref node p, ref node t)

//  infer [G] requires p::lseg_one<_>   ensures G(p,p');
  infer [H,G] requires H(p)   ensures G(p,p');
//  requires p::lseg_one<_> ensures p'::lseg_one<_> ; //'
{
  if (bool_nondet()) {
    t = new_node();
    t.h = 1;
    t.next = p;
    p = t;
    create_one(p,t);
  }
}


/*
can not reverify
*********************************************************
*******relational definition ********
*********************************************************
[ H(p') ::= H(p) * p'::node<v_int_37_1478,p>@M
 or emp&p'=DP_DP_DP_1489'
 (4,5),
 G(p,p') ::= DP_1488(p)&p'=p(4,5),
 DP_1488(p_1508) ::= H(p_1507) * p_1508::node<v_int_37_1509,p_1507>@M
 or emp&p_1508=DP_DP_DP_1489'
 (4,5)]
*************************************

 */
