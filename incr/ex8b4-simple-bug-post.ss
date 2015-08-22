/* Build a list of the form 1->...->1->0 */

data node {
 int h;
 node next;
}

bool bool_nondet()
  requires emp & true ensures emp & true;

node new_node()
  requires emp & true ensures res::node<_,_>;

HeapPred H1(node x, node b). // non-ptrs are @NI by default
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

lseg_one<p> == self=p
  or self::node<1,q>*q::lseg_one<p>
  ;

// lemma_safe self::lseg_one<t> * t::node<1,p> -> self::lseg_one<p>.

// please tighthen input/output consideration for method
// which are input only and which are output only, or both.
void create_one (ref node p)

//  infer [G] requires p::lseg<>   ensures G(p,p');
//  infer [G] requires p::lseg1<_>   ensures G(p,p');
//  infer [G1] requires p::lseg1<_>   ensures G1(p,p',t,t');
// infer [H,G] requires H(p,t)   ensures G(p,p',t,t');
// infer [H] requires H(p)   ensures true;
//  infer [H1] requires H1(p,t)   ensures true;
  requires p::lseg_one<q> 
  ensures p'::lseg_one<r> & r=q  ; //'
//  requires emp
//  ensures p'::lseg_one<p>  ; //'
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
# ex8b3

  requires p::lseg_one<q> 
  ensures p'::lseg_one<q>  ; //'

# Was a false generated for post-condition proving?

Checking procedure create_one$node... 
[UNSOUNDNESS] WARNING : new unsatisfiable state from post-proving of ex8b3-simple-bug-post.ss_49:10_49:25

// pre-cond proving
 p'::node<1,r>*r::lseg_one<q>  |- p::lseg_one<q> 

// post-cond proving:

  p'::lseg_one<q>  |-  p'::lseg_one<q>

*/
