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

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x,  node b).

ll_one<> == self=null
  or self::node<1,q>*q::ll_one<>
  ;

lseg<> == true
  or self::node<_,q>*q::lseg<>
  ;

lseg1<p> == self=p
  or self::node<_,q>*q::lseg1<p>
  ;

rlseg<p> == self=p
  or self::rlseg<q> * q::node<1,p>
  ;

lseg_one<p> == self=p
  or self::node<1,q>*q::lseg_one<p>
  ;

pred_prim Dang<>;

Q1<> == self::Dang<>
  or self::node<_,q>*q::Q1<>;

Q2<> == self::Q1<>
  ;

lemma_safe self::lseg_one<t> * t::node<1,p> -> self::lseg_one<p>.

HeapPred H1(node x, node@NI b). // non-ptrs are @NI by default
PostPred G1(node x,  node b,  node c, node d). // non-ptrs are @NI by default

  HeapPred P1(node p).
  PostPred P2(node p,node q).

// please tighthen input/output consideration for method
// which are input only and which are output only, or both.
void create_one (ref node p)
  infer [P1,P2]
  requires P1(p)
  ensures P2(p,p');
  /*
  requires p::Q1<>
  ensures p'::Q2<>;
*/
{
  node t;
  if (bool_nondet()) {
    t = new_node();
    t.h = 1;
    t.next = p;
    p = t;
    create_one(p);
  }
}

/*
# ex8d3.ss

  infer [P1,P2]
  requires P1(p)
  ensures P2(p,p');

# Why did we have two requires?

 infer[ P1,P2]requires P1(p)&truerequires emp
 ensures P2(p,p')&
true{,(4,5)=__norm#E};

# What are these warnings?

[solver.ml] Warning: normalize_w_coers expecting DataNode, ViewNode or HTrue
[solver.ml] Warning: normalize_w_coers expecting DataNode, ViewNode or HTrue
[solver.ml] Warning: normalize_w_coers expecting DataNode, ViewNode or HTrue
[solver.ml] Warning: normalize_w_coers expecting DataNode, ViewNode or HTrue
[solver.ml] Warning: normalize_w_coers expecting DataNode, ViewNode or HTrue

Given:
=====

[ // PRE_REC
(1;0)P1(p) * p'::node<v_int_70_1683,p>@M&true --> P1(p')&true,
 // POST
(1;0)P2(t_1689,p')&t_1689!=null --> P2(p,p')&true,
 // POST
(2;0)P1(p)&p'=p --> P2(p,p')&true]

Can we derive something simpler?
However, any assumptions are slightly wrong, and
we should obtain instead:

 PRE_REC: 
  emp --> P1(p')
 POST:  
  P2(t_1689,p')  *  t_1689::node<v_int_70_1683,p> &t_1689!=null 
           --> P2(p,p')
 POST:
  p'=p --> P2(p,p')

 (1;0)P1(p) * p'::node<v_int_70_1683,p>@M&true --> P1(p')&true,



 P1<> == dangling
 P2<p> == self=p
  or self::P2<t>*t::node<_,p>


# Why dod we not derive below?

Q1<> == self::Dang<>
  or self::node<_,q>*q::Q1<>;

Q2<p> == self::Q1<>
  ;




*/

