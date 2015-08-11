
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


  lseg_one<p> == self=p or self::node<1,q>*q::lseg_one<p>;
  ll_not_one<> == self=null or self::node<v,q>*q::ll<> & v!=1;


bool check_ones(node x)

  requires x::lseg_one<p>*p::ll_not_one<>
  ensures x::lseg_one<p>*p::ll_not_one<> & (res & p=null | !res & p!=null);

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
# ex3b4.ss

  lseg_one<p> == self=p or self::node<1,q>*q::lseg_one<p>;
  ll_not_one<> == self=null or self::node<v,q>*q::ll<> & v!=1;


  requires x::lseg_one<p>*p::ll_not_one<>
  ensures x::lseg_one<p>*p::ll_not_one<> & (res & p=null | !res & p!=null);


This strongest spec verifies and could be our target for inference


*/
