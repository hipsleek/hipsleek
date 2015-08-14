
data node {
 int val;
 node next;
}

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x). // non-ptrs are @NI by default

/*
sortll<n> == self=null
 or self::node<v,q>*q::sortll<v> & n<=v
 inv true; 
*/

  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;

  gg<p> == self=null or self=p or self::node<_,q>*q::gg<p>;

relation R(bool b,node p).

bool check_ones(node x)

  infer [R]
  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & R(res,p);

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
# ex3b2.ss

  infer [R]
  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & R(res,p);

GOT
===
!!! **pi.ml#775:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#776:>>REL POST:  R(res,p)
!!! **pi.ml#777:>>POST:  (not(res) | (p=null & res))
!!! **pi.ml#778:>>REL PRE :  true
!!! **pi.ml#779:>>PRE :  true

Can we get a stronger:
    !!! **pi.ml#777:>>POST:  (not(res) & p!=null | (p=null & res))


 */
