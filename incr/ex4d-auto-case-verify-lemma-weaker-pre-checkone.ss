data node {
 int val;
 node next;
}

  ll3<> == self=null 
          or self::node<1,q>*q::ll3<>
          or self::node<v,q>*q::ll3<> & v!=1;

  ll<> == self=null 
    or self::node<_,q>*q::ll<>;

  lseg_one<p> == self=p or self::node<1,q>*q::lseg_one<p>;


  ll_not_one<> == self=null or self::node<v,pp>*pp::ll<> & v!=1;
  ll_not_one3<> == self=null or self::node<v,pp>*pp::ll3<> & v!=1;


lemma_safe "ll3" self::ll3<> <-> self::lseg_one<p>*p::ll_not_one3<>.

lemma_safe "ll"  self::ll<> <-> self::lseg_one<p>*p::ll_not_one<>.

/*
# ex4d.ss

# Can we introduce automatic case-analysis?
  This occurs when RHS contains a disjunctive condition that cannot
  be proven by the current state.

lemma_safe "ll"  self::ll<> <-> self::lseg_one<p>*p::ll_not_one<>.

Entailing lemma ll: Fail. Details below:
	 "==>" implication: : Fail. (no cex)(may) cause:  true |-  v_1485!=1. LOCS:[0;16] (may-bug)
	 "<==" implication: : Valid.


 */
