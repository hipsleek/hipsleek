/* singly linked lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1 & S=union(S1, {v});

relation A(int a, bag b, bag c).

/* function to delete the a-th node in a singly linked list */
node delete2(node x, int a)
  infer [A]
  requires x::ll2<n,S>
  ensures res::ll2<m,S1> & m<=n & A(a,S,S1);//& (a notin S & S = S1 | S=union(S1, {a}));
{
	if (x == null)
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete2(x.next, a));
	}
}
