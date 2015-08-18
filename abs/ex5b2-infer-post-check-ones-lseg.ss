
data node {
 int val;
 node next;
}

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x). // non-ptrs are @NI by default

  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;

  lseg_ones<p> == self=p or self::node<1,q>*q::lseg_ones<p>;
  ll_not_one<> == self=null or self::node<v,q>*q::ll<> & v!=1;

relation RRR(node x,bool y).

bool check_ones(node x)
/*
# verifies..

  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & (res & p=null | !res & p!=null);

  requires x::ll<>
  ensures x::lseg<p>*p::ll<> ;

  requires x::ll<>@L
  ensures x::lseg<p>@A*p::ll<>@A ;

  requires x::ll<>@L
  ensures x::lseg<p>@A*p::ll<>@A & (res & p=null | !res & p!=null);

  // free lemma
  x::ll<> <--> x::lseg<p>*p::ll<>
          <--> x::lseg_ones<p>*p::ll_not_one<>

  requires x::lseg<p>@*p::ll<>@L
  ensures (res & p=null | !res & p!=null);

   requires x::ll<>@L
  ensures x::lseg_ones<p>@A*p::ll_not_one<>@A 
           & (res & p=null | !res & p!=null);

  requires x::ll<>
  ensures x::lseg_ones<p>*p::ll_not_one<> 
           & (res & p=null | !res & p!=null);

  requires x::lseg_ones<p>@L*p::ll_not_one<>@L
  ensures (res & p=null | !res & p!=null);

Fails
-----
  requires x::ll<>@L
  ensures x::lseg<p>@A*p::ll<>@A & (res & p!=null | !res & p=null);
*/

  infer [RRR,@imm_pre,@imm_post]
//  infer [RRR]
  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & RRR(p,res);

{
  if (x==null) return true;
  else {
   int t = x.val;
   if (t==1) return check_ones(x.next);
   else {
      //dprint;
       return false;
   }
 }
} 

/*
# ex5b2.ss

  infer [RRR]
  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & RRR(p,res);

-tp z3 added RRR for the above

# Did you add new unknown relation to Cast.prog_rel_decls?

;Variables declarations
(declare-fun v_bool_67_1434_primed () Int)
(declare-fun v_bool_64_1435_primed () Int)
(declare-fun x_primed () Int)
(declare-fun x () Int)
(declare-fun Anon_1453 () Int)
(declare-fun t_primed () Int)
(declare-fun v_node_67_1431_primed () Int)
(declare-fun q_1454 () Int)
(declare-fun p_1470 () Int)
(declare-fun res () Int)
;Relations declarations
(declare-fun RRR (Int Int) Bool)
;Axioms assertions
;Antecedent
(assert (= v_node_67_1431_primed 1))
(assert (> v_bool_67_1434_primed 0))
(assert (not (> v_bool_64_1435_primed 0)))
(assert (> x_primed 0))
(assert (= x_primed x))
(assert (= t_primed Anon_1453))
(assert (= t_primed 1))
(assert (= v_node_67_1431_primed q_1454))
(assert (RRR p_1470 res))
;Negation of Consequence
(assert (not false))
(check-sat)


*/
