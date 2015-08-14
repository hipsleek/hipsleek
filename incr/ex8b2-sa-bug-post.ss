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


// please tighthen input/output consideration for method
// which are input only and which are output only, or both.
void create_one (ref node p)

//  infer [G] requires p::lseg<>   ensures G(p,p');
//  infer [G] requires// p::lseg1<_>   ensures G(p,p');
//  infer [G1] requires p::lseg1<_>   ensures G1(p,p',t,t');
// infer [H,G] requires H(p)   ensures G(p,p');
// infer [H] requires H(p)   ensures true;
//  infer [H1] requires H1(p,t)   ensures true;
//  requires p::lseg_one<q> 
//  ensures p'::lseg_one<q>  ; //'
                            /*
  requires true
  ensures p'::lseg_one<p>  ; //'
                            */
// infer [H] requires H(p)   ensures true;
 infer [G] requires true   ensures G(p,p');
  /*
 requires true
  ensures p'::rlseg<p>  ;
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
*************************************
*******shape relational assumptions ********
*************************************
[ // POST
(1;0)(htrue) * t_1668::node<v_int_69_1662,p>@M * G(t_1668,p')&
true --> G(p,p')&
true,
 // POST
(2;0)htrue&p'=p --> G(p,p')&
true]

*********************************************************
*******relational definition ********
*********************************************************
[ G(p_1669,p_1670) ::= htrue&p_1670=p_1669(4,5)]
*************************************


TODO:
 - detect this scheme (i.e. pre in pre-fix form)
 - infer pre -> true
 - re-verify + infer post
 */


                                        /*
pred rlseg<p> == self=p
  or self::node<_,q> * q::rlseg<p>.


                                         */
