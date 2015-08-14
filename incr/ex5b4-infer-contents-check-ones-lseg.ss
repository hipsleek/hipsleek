
data node {
 int val;
 node next;
}

HeapPred H(node x). // non-ptrs are @NI by default
PostPred G(node x). // non-ptrs are @NI by default

  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;

relation R(node x,bool y).

relation R1(int n).
relation R2(int n).

lseg_ones<p> == self=p or self::node<v,q>*q::lseg_ones<p> & R1(v);
ll_not_one<> == self=null or self::node<v,q>*q::ll<> & R2(v);


bool check_ones(node x)

  infer [R1,R2]
  requires x::ll<>
  ensures x::lseg_ones<p>*p::ll_not_one<> 
      & (!(res) & p!=null | (p=null & res));

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
# ex5b4.ss

  infer [R1,R2]
  requires x::ll<>
  ensures x::lseg_ones<p>*p::ll_not_one<> 
      & (!(res) & p!=null | (p=null & res));
lseg_ones<p> == self=p or self::node<v,q>*q::lseg_ones<p> & R1(v);
ll_not_one<> == self=null or self::node<v,q>*q::ll<> & R2(v);


# Obtain:

[RELDEFN R1(__norm#E): ( v_1495=1) -->  R1(v_1495),
RELDEFN R1(__norm#E): ( v_1505!=1) -->  R1(v_1505),
RELDEFN R2(__norm#E): ( v_1514!=1) -->  R2(v_1514),
RELDEFN R2(__norm#E): ( true) -->  R2(v_1517)]

# Is this correct?
# Should it be just:

   v=1 --> R1(v)
   v!=1 --> R2(v)

# Why did we have spurious relations?

*/
