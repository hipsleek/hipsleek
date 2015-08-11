
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

relation R(node x,bool y).

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

  infer [R]
  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & R(p,res);

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

  infer [R]
  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & R(p,res);

# Obtain:

!!! **pi.ml#775:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#776:>>REL POST:  R(p,res)
!!! **pi.ml#777:>>POST:  (not(res) | (p=null & res))
!!! **pi.ml#778:>>REL PRE :  true
!!! **pi.ml#779:>>PRE :  true


# Can we derive a stronger:

  (not(res) & p!=null | (p=null & res))

*/