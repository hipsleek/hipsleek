data node{
	int val;
	node prev;
	node next;
}

void set_tail (node c,node y)
  requires c::node<_@A,_@A,_@M>
  ensures  c::node<_@A,_@A,y>;
{
   c.next = y;
}

