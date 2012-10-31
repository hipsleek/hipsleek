data node {
	int val;
	node next;
}

int front(node x)
  requires x::node<a,_>
  ensures htrue ;
{
  return x.val;
}

