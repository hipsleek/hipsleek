data node {
 int val;
 node next;
}

  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;


bool check_ones(node x)
  infer [@imm_pre,@imm_post] 
  requires x::ll<>
  ensures x::ll<>;
  requires x::lseg<p>*p::ll<>
  ensures x::lseg<p>*p::ll<>;


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
# ex5b.ss

Can we infer the immutability of the following specs?

  requires x::ll<>
  ensures x::ll<>;
  requires x::lseg<p>*p::ll<>
  ensures x::lseg<p>*p::ll<>;

*/
