
data node {
 int val;
 node next;
}


  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;

  gg<p> == self=null or self=p or self::node<_,q>*q::gg<p>;

  ll_one<> == self=null or self::node<1,q>*q::ll_one<>;
  lseg_one<p> == self=p or self::node<1,q>*q::lseg_one<p>;

// higher-order predicate
relation R(int r).

llR<R> == self=null or self::node<v,q>*q::llR<R> & R(v);
lsegR<R,p> == self=p or self::node<v,q>*q::lsegR<R,p> & R(v);

relation R1(int r) == r=1.
relation R2(int r).

bool check_ones(node x)
  requires x::ll<>
  ensures x::llR<R1> & res or x::lsegR<R1,p>*p::ll<> & !res;
{ 
  if (x==null) return true;
  else {
   int t = x.val;
   if (t==1){
     return check_ones(x.next);
   }
   else {
      //dprint;
       return false;
   }
 }
} 

/*
# ex3f1.ss

  requires x::ll<>
  ensures x::llR<R1> & res or x::lsegR<R1,p>*p::ll<> & !res;

# not sure why fail. need to check if pred built correctly.

Context of Verification Failure: ex3f1-verify-content-check-all-ones-ll-lseg.ss_28:10_28:26

Last Proving Location: ex3f1-verify-content-check-all-ones-ll-lseg.ss_36:14_36:19

ERROR: at ex3f1-verify-content-check-all-ones-ll-lseg.ss_28:10_28:26
Message: Post condition cannot be derived.

Procedure check_ones$node FAIL.(2)


Exception Failure("Post condition cannot be derived.") Occurred!

==========================
# Not enough type info for relation..

 view lsegR{}[]<R:RelT([]),p:node>= 
  view_domains: 
   view lsegR<R:RelT([]),p:node>= 
    EList
      :EBase 
         (* lbl: *){222}->emp&self=p&{FLOW,(1,28)=__flow#E}[]
      || :EBase 
            exists (Expl)[](Impl)[v; 
            q](ex)[](* lbl: *){223}->(exists p_24: (* lbl: *){223}->self::node<v,q>@M * 
                                                                    q::lsegR<R,p_24>@M&
            R(v) & p_24=p&{FLOW,(1,28)=__flow#E}[]

# Did R1 capture r=1? Can print?

 relation R1(int r).

# what are these warnings for?

WARNING: _0:0_0:0:Z3 error message: (error "line 3427 column 29: unknown function/constant R1_1553")

# maybe we can try with simpler examples involving
  2nd-order verification..

*/
