data node {
 int val;
 node next;
}


void join(node x, node y)
  infer [@imm]
  requires x::node<a1,n1>*y::node<a2,n2>
  ensures x::node<a1,y>*y::node<_,_> ;
{ 
  x.next = y;
} 

/*
# ex6b.ss

From:

  infer [@imm]
  requires x::node<a1,n1>*y::node<a2,n2>
  ensures x::node<a1,y>*y::node<_,_> ;

Can we derive:
 
  requires x::node<a1@L,_>*y::node<_,_>@A
  ensures x::node<a1,y> ;


*/
