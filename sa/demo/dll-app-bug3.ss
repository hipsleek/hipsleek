data node{
	node next;
	node prev;
}

void dll_append(node l1, node l2)
//requires l1::node<_,null> & l2!=null  ensures false;
requires l1::node<_,a> & l2!=null  ensures l1::node<l2,a>;
{
	l1.next = null;
	l1.next = l2;
}

/* FIXED
  should not allow me to prove false, seems like a substitution problem
*/

