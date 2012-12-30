/* singly linked lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<S> == self = null & S = {} 
	or self::node<v, q> * q::ll<S1> & S = union(S1, {v});

relation A(bag a, bag b, bag c).

/* append two singly linked lists */
void append(node x, node y)
  infer [x,A]
	requires x::ll<S1> * y::ll<S2>// & x != null
	ensures x::ll<S> & A(S1,S2,S); //& S = union(S1, S2);

{
	if (x.next==null)
    {      
      x.next = y;
      //dprint;
      //assume false;
    }
	else
   {
    //assume false;
		append(x.next, y);
    }
}
