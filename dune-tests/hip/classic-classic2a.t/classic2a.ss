data node {
	int val;
	node next;
}

int foo2(node x)
  requires x::node<_,_>
  ensures_exact emp;
{
  return x.val;
}

int foo1(node x)
  requires x::node<_,_>
  ensures_exact htrue;
{
  return x.val;
}
