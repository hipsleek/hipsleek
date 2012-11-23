/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n, S> == self = null & n = 0 & S = {}
	or self::node<v, q> * q::ll<n-1, S1> & S = union(S1, {v}) 
  inv n >= 0;
  
lseg<p, n, S> == self=p & n=0 & S = {}
	or self::node<v, q> * q::lseg<p, n-1, S1> & S = union(S1, {v})
	inv n>=0;

node append3(node x, node y)
  requires x::lseg<null, n, S> 
  ensures res::lseg<y, n, S>;
{
	if (x == null) 
		return y;
	else {
		//assume false;
		node tmp = x.next;
		x.next = append3(tmp, y);
		return x;
	}
}

/* append two singly linked lists */
void append2(node x, node y)
  requires x::ll<n1, S1> * y::ll<n2, S2> & x!=null
  ensures x::ll<n1+n2, S> & S = union(S1, S2);
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}


void append(node x, node y)
  requires x::ll<n1, S1> * y::ll<n2, S2> & n1>0
  ensures x::ll<n1+n2, S> & S = union(S1, S2);
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

/* return the first element of a singly linked list */
node ret_first(node x)

	requires x::ll<n, S> * y::ll<m, _> & n < m 
	ensures x::ll<n, S>;

{
	return x;
}

/* return the tail of a singly linked list */
node get_next(node x)

	requires x::ll<n, S> & n > 0
	ensures x::ll<1, S1> * res::ll<n-1, S2> & S  = union(S1, S2); 

{
	node tmp = x.next;
    x.next = null;
	return tmp;
}

/* function to set the tail of a list */
 void set_next(node x, node y)
	/*
	requires x::ll<i, S1> * y::ll<j, S2> & i > 0 
	ensures x::ll<j+1, S> & S = union({x.val}, S2); 
	*/
	requires x::node<v, _> * y::ll<j, S1>  
	ensures x::ll<j+1, S> & S = union({v}, S2); 
{
	x.next = y;
}


/* function to set null the tail of a list */
void set_null(node x)

	requires x::node<v, _>
	ensures x::ll<1, {v}>;

{
	x.next = null;
}

/* function to get the third element of a list */
node get_next_next(node x) 

	requires x::ll<n, _> & n > 1
	ensures res::ll<n-2, _>;

{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)
	requires x::ll<n, S> & n > 0 
	ensures x::ll<n+1, S1> & S1 = union(S, {a});
{

    node tmp = null;
	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
	requires x::ll<n, _> & n > a & a > 0 
	ensures x::ll<n-1, _>;
{
    if (a == 1)
	{
		x.next = x.next.next;
	}
	else
	{
		delete(x.next, a-1);
	}	
}


node delete1(node x, int a)
	requires x::ll<n, S>  
	case {
		a notin S -> ensures res::ll<n, S>;
		a in S -> ensures res::ll<n-1, S1> & S = union(S1, {a});
	}
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}

/* function to create a singly linked list with a nodes */
node create_list(int a)
	requires a >= 0 
	ensures res::ll<a, S> & forall(x: (x notin S | x = 0));

{
	node tmp;

	if (a == 0) {
		return null;
	}
	else {    
		a  = a - 1;
		tmp = create_list(a);	
		return new node (0, tmp);
	}	
}

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)
	requires xs::ll<n, S1> * ys::ll<m, S2> 
	ensures ys'::ll<n+m, S> & xs' = null & S = union(S1, S2);
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		reverse(xs, ys);
	}
}
