data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1>;

/* function to insert a node in a singly linked list */
void insert(node x, int a)
	requires x::ll<n> & n > 0 
	ensures x::ll<n+1>;
{
  if (x.next == null)
 		x.next = new node(a, null);
	else
  insert(x.next.next, a);
  // insert(x.next, a);
} 
