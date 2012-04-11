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

/* functions to count the number of nodes in a circular list */
int count_rest(node rest, node h)
    infer [A]
    requires rest::cll<p, n> & h = p 
    ensures rest::cll<p, n> & res = n; 

int count(node x)
	infer [A]
	requires x::hd<n>
	ensures x::hd<n> & A(res,n); //res = n; 
	
{
	int n;

	if (x == null)
		return 0;
	else 
	{
		n = count_rest(x.next, x);
		n = n + 1;

		return n;
	}
}
