// $ ../hip ex5b1-infer-shape-check-ones-lseg.ss --pred-en-seg

data node {
 int val;
 node next;
}

relation R(node x,bool y).

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x). // non-ptrs are @NI by default

  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;

  lseg_ones<p> == self=p or self::node<1,q>*q::lseg_ones<p>;
  ll_not_one<> == self=null or self::node<v,q>*q::ll<> & v!=1;


bool check_ones(node x)
  infer [H,G]
  requires H(x)
  ensures G(x);

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

