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

	
	

/* return the tail of a singly linked list */
node get_next(node x)

	/* requires x::ll<n> & n > 0 */
	/* ensures x::ll<1> * res::ll<n-1>;  */
  requires x::node<v,q>
  ensures x::node<v,null> & res=q;
  requires x=null 
  ensures x=null & flow __Error;

{
    dprint;
	node tmp = x.next;
	x.next = null;
	return tmp;
}







