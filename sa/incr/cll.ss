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

HeapPred H(node a, node b).
HeapPred G(node a, node b).

/* functions to count the number of nodes in a circular list */
int count_rest(node rest, node h)
/*
   infer [H,G] 
   requires H(rest,h)
   ensures G(rest,h);
*/
infer [@shape] requires true ensures true;
/*
	requires rest::cll<p, n> & h = p 
	ensures rest::cll<p, n> & res = n; 
*/

{
	int n;
	
	if (rest == h)
		return 0; 
	else
	{
		n = count_rest(rest.next, h);
		n = n + 1;

		return n;
	}
}

