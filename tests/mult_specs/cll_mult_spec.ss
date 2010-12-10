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

cll1<p, S> == self = p & S = {}
	or self::node<v, r> * r::cll1<p, S1> & self != p & S = union(S1, {v});  

hd1<S> == self = null & S = {}
	or self::node<v, r> * r::cll1<self, S1> & S = union(S1, {v});

cll2<p, n, S> == self = p & S = {} & n = 0
	or self::node<v, r> * r::cll2<p, n-1, S1> & self != p & S = union(S1, {v});  

hd2<n, S> == self = null & S = {} & n = 0
	or self::node<v, r> * r::cll2<self, n-1, S1> & S = union(S1, {v});

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
	//********************** MULTI PRE/POST *******************************************
	
	requires x::hd<n> & n > 0 
	ensures x::hd<n+1>;
	
	requires x::hd1<S> & S != {} 
	ensures x::hd1<S1> & S1 = union(S, {v});
	
	//********************** SINGLE PRE/POST *******************************************
  	//requires x::hd2<n, S> & S != {} 
	//ensures x::hd2<n+1, S1> & S1 = union(S, {v});

{
	node tmp;

	tmp = new node(v, x.next);

	x.next = tmp;
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
	//********************** MULTI PRE/POST *******************************************	
	
	requires x::hd<n> & n > 0
	ensures x'::hd<n-1>;
	
	requires x::hd1<S> & S != {}
	ensures x'::hd1<S1>;
	
	//********************** SINGLE PRE/POST *******************************************
	//requires x::hd2<n, S> & S != {}
	//ensures x'::hd2<n-1, S1>;

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


