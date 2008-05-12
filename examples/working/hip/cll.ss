/* circular lists */

/* representation of a node */
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


node test() 
	requires true
	ensures true;
{
	node null_tmp = null; 
	node tmp = new node(10, null_tmp);

	//assert tmp'::cll<_, 1>;

	//assert tmp'::node<_, r> * r::cll<r, 0> assume;

	tmp.next = tmp;

	node tmp2 = new node(20, tmp.next);
	tmp.next = tmp2;

	//assert tmp'::hd<2>;

	return tmp;
}

void insert(node x, int v)
	
	requires x::hd<n> & n > 0 
	ensures x::hd<n+1>;

{
	node tmp;

	tmp = new node(v, x.next);

	x.next = tmp;

	


	//assert tmp'::cll<x',n>;
	//debug on;
	//assert x'::hd<_>;
	//assert x'::node<_, r> * r::cll<x', _>;
	//debug off;
}

 
/*
/* insert a node in a circular list after the head */
void insert(node x, int v)
	
	requires x::hd<n> & n > 0 
	ensures x::hd<n+1>;

{
	x.next = new node(v, x.next);
}
*/

/* functions to count the number of nodes in a circular list */
int count_rest(node rest, node head)

	requires rest::cll<p, n> & head = p 
	ensures rest::cll<p, n> & res = n; 

{
	int n;
	
	if (rest == head)
		return 0; 
	else
	{
		n = count_rest(rest.next, head);
		n = n + 1;

		return n;
	}
}

int count(node x)
	
	requires x::hd<n>
	ensures x::hd<n> & res = n; 
	
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

	requires x::hd<n> & n > 0
	ensures x'::hd<n-1>;

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


