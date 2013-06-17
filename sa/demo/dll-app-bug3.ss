data node{
	node next;
	node prev;
}

void dll_append(node l1, node l2)
requires l1::node<_,null> & l2!=null  ensures false;
{
	l1.next = null;
	l1.next = l2;
}

/*
  should not allow me to prove false, seems like a substitution problem
*/

