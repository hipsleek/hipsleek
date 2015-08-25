
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
relation R(bool r).

llR<R> == self=null or self::node<v,q>*q::ll<R> & R(v);
lsegR<R,p> == self=p or self::node<v,q>*q::lsegR<R,p> & R(v);

relation R1(int r).
relation R2(int r).

bool check_ones(node x)
  infer [R1,R2]
  requires x::ll<>
  ensures x::llR<R1> & res or x::lsegR<R2,p>*p::ll<> & !res;
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
# ex3e.ss

  requires x::ll<>
  ensures x::ll_one<> & res or x::lseg_one<p>*p::ll<> & !res;

  ll<> == self=null or self::node<_,q>*q::ll<>;
  ll_one<> == self=null or self::node<1,q>*q::ll_one<>;
  lseg_one<p> == self=p or self::node<1,q>*q::lseg_one<p>;

verifies!

*/
