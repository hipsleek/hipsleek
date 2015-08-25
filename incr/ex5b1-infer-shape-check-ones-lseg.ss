// $ ../hip ex5b1-infer-shape-check-ones-lseg.ss --pred-en-seg

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

/*
# ex5a.ss

  infer [H,G]
  requires H(x)
  ensures G(x);

# Obtain:

[ H(x_1470) ::= H(next_58_1468) * x_1470::node<val_58_1471,next_58_1468>@M
 or emp&x_1470=null
 (4,5),
 G(x_1472) ::= x_1472::node<val_58_1473,next_58_1447>@M * G(next_58_1447)
 or x_1472::node<val_58_1474,next_58_1447>@M * H(next_58_1447)
 or emp&x_1472=null
 (4,5)]
*************************************

!!! INFERRED SHAPE SPEC:
 EBase 
   x::H<>@M&{FLOW,(4,5)=__norm#E}[]
   EBase 
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       x::G<>@M&{FLOW,(4,5)=__norm#E}[]Stop z3... 108 invocations 

# Can we transform to:

  requires x::ll<>
  ensures x::lseg<p>*p::ll<> ;


*/
