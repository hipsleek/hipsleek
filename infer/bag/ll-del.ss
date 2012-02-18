/* singly linked lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<S> == self = null & S = {} 
	or self::node<v, q> * q::ll<S1> & S = union(S1, {v});

relation A(int a, bag b, bag c).

/* function to delete the a-th node in a singly linked list */
node delete1(node x, int a)
  infer [A]
	requires x::ll<S>  
	ensures res::ll<S1> & A(a,S,S1);//& (a notin S & S = S1 | S=union(S1, {a}));
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}
