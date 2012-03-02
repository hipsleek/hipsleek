/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


/* accessing and disposing first two nodes */
node foo(node x)
    //infer [n]
   requires x::ll<n> & n>1 
    ensures true;

{
	node tmp = x.next;
    dprint;
    dispose(x);
    dprint;
	x = tmp.next;
    dprint;
    dispose(tmp);
    dprint;
	return tmp;
}

void dispose(node x)
    //infer [n]
  requires x::node<_,_>
  ensures true;

