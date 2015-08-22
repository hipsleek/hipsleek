/* Build a list of the form 1->...->1->0 */

data node {
 int h;
 node next;
}

bool bool_nondet()
  requires emp & true ensures emp & true;

node new_node()
  requires emp & true ensures res::node<_,_>;

HeapPred H1(node x, node@NI b). // non-ptrs are @NI by default
 PostPred G1(node x,  node b,  node c, node d). // non-ptrs are @NI by default


Q3<p> == self=p or self::Q3<t>*t::node<_,p>
  ;

lseg_one<p> == self=p
  or self::node<_,q>*q::lseg_one<p>
  ;


HeapPred H2(node x). // non-ptrs are @NI by default

// please tighthen input/output consideration for method
// which are input only and which are output only, or both.
void create_one (ref node p)
/*
  requires emp
  ensures p'::Q3<p>;  
  requires p::lseg_one<rr>
  ensures p'::lseg_one<rr>;
*/
  infer [H2]
  requires H2(p)
  ensures true;

{
  node t;
  if (bool_nondet()) {
    //assume false;
    t = new_node();
    t.h = 1;
    t.next = p;
    p = t;
    // t::node<1,p>*p::Q3<rr>&p'=t |- p'::Q3<rr2>
    create_one(p);
    // p'::Q3<rr2> & rr2=rr
  }
}

/*
# ex8d7.ss

  H2(p) = p::node<_,_> *...

[ // PRE_REC
(1;0)H2(p) * p'::node<v_int_46_1480,p>@M&true --> H2(p')&
true]

   infer [H2] H2(p) & p=p' |- true

Given:

  requires emp
  ensures p'::Q3<p>;

  Q3<p> == self=p or self::Q3<t>*t::node<_,p>

Verification currently fails:

  infer [P2]
  requires emp
  ensures P2(p',p);

Can we mWe derived:

[ // POST
(1;0)t_1688::node<v_int_66_1682,p>@M * P2(p',t_1688)&true --> P2(p',p)&
true,
 // POST
(2;0)emp&p'=p --> P2(p',p)&
true]

This should generate:

 t::node<_,p>@M * P2(p',t) \/ p'=p--> P2(p',p)

# Why did we just get:

  [ P2(p_1689,p_1690) ::= emp&p_1689=p_1690(4,5)]

We should be expecting:

 P2(p',p) == p'=p \/ P2(p',t) * t::node<_,p>

   which corresponds to the spec:

Q2<p> == self=p or self::Q2<t>*t::node<_,p>

*/

