/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
cll<p, n> == self = p & n = 0
	or self::node<_, r> * r::cll<p, n-1> & self != p  
	inv n >= 0;

hd<n> == self = null & n = 0
	or self::node<_, r> * r::cll<self, n-1>  
	inv n >= 0;


void insert(node x, int v)
	requires x::hd<n> & n > 0 
	ensures x::hd<n+1>;
{
	node tmp;

	tmp = new node(v, x.next);
	x.next = tmp;
        dprint;	
}




