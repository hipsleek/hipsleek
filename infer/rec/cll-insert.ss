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


relation A(int x, int y).
relation B(node x, node y). // can i have?

void insert(node x, int v)
	infer [n,A]
	requires x::hd<n> //& n > 0 
	ensures x::hd<m> & A(m,n);
{
	node tmp;

	tmp = new node(v, x.next);
    //dprint;
	x.next = tmp;
	//dprint;
	//assert x'::hd<m>;
	//assume false;
}
