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


