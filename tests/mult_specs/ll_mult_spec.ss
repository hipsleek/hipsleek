/* singly linked lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n1> & n = n1 + 1
	inv n >= 0;

ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});

ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});

/* append two singly linked lists */
void append(node x, node y)
	//********************** MULTI PRE/POST *******************************************
	/*
  	requires x::ll<n1> * y::ll<n2> & x != null
  	ensures x::ll<n1 + n2>;

  	requires x::ll1<S1> * y::ll1<S2> & x != null
  	ensures x::ll1<S> & S = union(S1, S2);
	*/
	//********************** SINGLE PRE/POST *******************************************
  	requires x::ll2<n1, S1> * y::ll2<n2, S2> & x != null
  	ensures x::ll2<n1+n2, S> & S = union(S1, S2); 
{
	if (x.next == null)
		x.next = y;
	else
		append(x.next, y);
}

/* return the first element of a singly linked list */
node ret_first(node x)

	requires x::ll<n> * y::ll<m> & n < m 
	ensures x::ll<n>;

{
	return x;
}

/* return the tail of a singly linked list */
node get_next(node x)

	requires x::ll<n> & n > 0
	ensures x::ll<1> * res::ll<n-1>; 

{
	node tmp = x.next;
	x.next = null;
	return tmp;
}

/* function to set the tail of a list */
 void set_next(node x, node y)

	requires x::ll<i> * y::ll<j> & i > 0 
	ensures x::ll<j+1>; 

{
	x.next = y;
}

/* function to set null the tail of a list */
void set_null(node x)

	requires x::ll<i> & i > 0 
	ensures x::ll<1>;

{
	x.next = null;
}

/* function to get the third element of a list */
node get_next_next(node x) 

	requires x::ll<n> & n > 1
	ensures res::ll<n-2>;

{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)
	//********************** MULTI PRE/POST *******************************************
	requires x::ll<n> & n > 0 
	ensures x::ll<n+1>;
	
	requires x::ll1<S> & S != {}
	ensures x::ll1<S1> & S1 = union(S, {a});
	//********************** SINGLE PRE/POST *******************************************  	
  	//requires x::ll2<n, S> & S != {}
	//ensures x::ll2<n+1, S1> & S1 = union(S, {a});
{
        node tmp = null;

	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
	requires x::ll<n> & n > a & a > 0 
	ensures x::ll<n - 1>;
{
        if (a == 1)
	{
		//node tmp = x.next.next;
		//x.next = tmp;
                  x.next = x.next.next;
	}
	else
	{
		delete(x.next, a-1);
	}	
}


/* function to create a singly linked list with a nodes */
node create_list(int a)
	requires a >= 0 
	ensures res::ll<a>;

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
	//********************** MULTI PRE/POST *******************************************	
	requires xs::ll<n> * ys::ll<m> 
	ensures ys'::ll<n+m> & xs' = null;
	
	requires xs::ll1<S1> * ys::ll1<S2> 
	ensures ys'::ll1<S3> & S3 = union(S1, S2) & xs' = null;
	//********************** SINGLE PRE/POST *******************************************	
	//requires xs::ll2<n1, S1> * ys::ll2<n2, S2> 
	//ensures ys'::ll2<n1+n2, S3> & S3 = union(S1, S2) & xs' = null;
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





