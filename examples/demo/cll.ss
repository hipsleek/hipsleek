/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
lseg<p, n> == self = p & n = 0
	or self::node<_, r> * r::lseg<p, n-1> & self != p  
	inv n >= 0;

cll<n> == self = null & n = 0
	or self::node<_, r> * r::lseg<self, n-1>  
	inv n >= 0;


void insert(node x, int v)
	
	requires x::cll<n> & n > 0 
	ensures x::cll<n+1>;
{
	node tmp;

	tmp = new node(v, x.next);
	x.next = tmp;
}



/* functions to count the number of nodes in a circular list */
int count_rest(node rest, node h)

	requires rest::lseg<p, n> & h = p 
	ensures rest::lseg<p, n> & res = n; 

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

int count(node x)
	
	requires x::cll<n>
	ensures x::cll<n> & res = n; 
	
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


/* function to delete the node after the head in a circular list */
void delete(ref node x)

	requires x::cll<n> & n > 0
	ensures x'::cll<n-1>;

{
	node tmp;

	if (x.next == x)
		x = null;
	else
	{
		tmp = x.next.next;
		x.next = tmp;
	}
}


