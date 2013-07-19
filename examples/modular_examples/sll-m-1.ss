/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 next;	
}

/* view for a doubly linked list with size */
dll<"n":n> == 
	self = null &["n":n = 0] or 
	self::node2<_ , q> * q::dll<n1> & ["n":n1=n-1]
	inv true & ["n":n >= 0];



void f1(node2 x)
	requires x::dll<m> & ["n":m>0]
	ensures x::dll<n> & ["n":n=m];
{
	int t = 0;
	t = t+1;
}

