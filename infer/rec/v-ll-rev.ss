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

/*
*/
	
	
relation A(node r,int x, int y, int z).

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)
//    infer [A]
	requires xs::ll<n> * ys::ll<m> 
    ensures ys'::ll<t> & t=m+n & xs'=null;
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
    //dprint;
		xs.next = ys;
		ys = xs;
		xs = tmp;
    //dprint;
		reverse(xs, ys);
	}
}
