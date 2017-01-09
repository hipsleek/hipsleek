
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


bool check_ones(node x)

/*  requires x::ll<>
  ensures x::ll<> or x::lseg<p>*p::ll<>;
  requires x::ll<>
  ensures x::lseg<p>*p::ll<>;
*/
  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & (res & p=null | !res & p!=null);
/*
  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & (res & p=null | !res);
*/

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
# ex3b1.ss

  requires x::ll<>
  ensures x::lseg<p>*p::ll<> & (res & p=null | !res & p!=null);

Above verifies!

Above seems a more concise spec to aim for ..

*/
