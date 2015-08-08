data node {
 int val;
 node next;
}


int join(node x, node y)
  infer [@imm]
  requires x::node<a1,n1>*y::node<a2,n2>
  ensures x::node<a1,n1>*y::node<_,_> & res=a1;
{ 
  return x.val;
} 

/*
# ex6c.ss

From:

  infer [@imm]
  requires x::node<a1,n1>*y::node<a2,n2>
  ensures x::node<a1,n1>*y::node<_,_> & res=a1;

Can we derive:
 
  infer [@imm]
  requires x::node<a1,n1>@L*y::node<a2,n2>@A
  ensures  res=a1;


*/
