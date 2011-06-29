data node {
	int val;
	node next;
}

/*
node f(node x)   {
	return f(null);
}
*/

void f2(node xs) 
 requires xs::node<_, y> * y::node<_, _>
 ensures true;
{
	xs.val = xs.next.val;
	xs.val = xs.val;

	int v = 1;
	xs.val = v;
}

void f3()
{
	node x;
	x = new node (10, null);
	bind x to (xv, xn) in {
		xv = 1;
		xn = new node (0, null);
	}
}
