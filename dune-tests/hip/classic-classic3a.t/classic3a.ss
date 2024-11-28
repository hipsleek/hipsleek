data node {
	int val;
	node next;
}

int foo2(node x)
  requires x::node<_,_>
  ensures_inexact emp;
{
  return x.val;
}

int foo1(node x)
  requires x::node<_,_>
  ensures_inexact htrue;
{
  return x.val;
}
