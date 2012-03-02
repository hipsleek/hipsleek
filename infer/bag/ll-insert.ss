/* singly linked lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<S> == self = null & S = {} 
	or self::node<v, q> * q::ll<S1> & S = union(S1, {v});

relation A(bag a, bag b, int c).

/* function to insert a node in a singly linked list */
void insert(node x, int a)
  infer [A]
	requires x::ll<S> & S != {}
	ensures x::ll<S1> & A(S,S1,a); //S1 = union(S, {a});

{
  node tmp = null;
	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 
