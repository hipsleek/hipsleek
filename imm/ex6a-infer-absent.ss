data node {
 int val;
 node next;
}

  ll<> == self=null or self::node<_,q>*q::ll<>;

  lseg<p> == self=p or self::node<_,q>*q::lseg<p>;


int join(node x, node y)
  infer [@imm]
  requires x::node<a1,_>*y::node<a2,_>
  ensures x::node<_,_>*y::node<_,_> & res=a1+a2;
{ 
  return x.val+y.val;
} 

/*
# ex6a.ss

Can we derive the spec:

  requires x::node<a1,_>@L*y::node<a2,_>@L
  requires res=a1+a2

How come no immutability inferred?

*/
