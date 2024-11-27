data node {
	int val;
	node next;
}

int foo2(node x)
  requires x::node<_,_>
  ensures emp;
{
  return x.val;
}

int foo1(node x)
  requires x::node<_,_>
  ensures htrue;
{
  return x.val;
}
