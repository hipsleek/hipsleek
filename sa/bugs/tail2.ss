data node{
	int val;
	node prev;
	node next;
}

node foo (node c)
  requires c::node<_@A,_@A,n@L>
  ensures  res=n;
{
   return c.next;
}

