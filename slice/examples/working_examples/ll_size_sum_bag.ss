data node {
  int val;
  node next;
}

/* view for singly linked list */

ll<n, s, S> ==
	self = null & n = 0 & s = 0 & S = {} or
	self::node<vvv, r> * r::ll<n1, s1, S1>
		& (vvv) >= 0
		& n = n1 + 1
		& s = s1 + ($ vvv)
		& S = union(S1, {($ vvv)})
	inv n >= 0 & s >= 0 & forall (xxx : (xxx notin S | xxx >= 0));

/*
ll<n, s> ==
	self = null & n = 0 & s = 0 or
	self::node<vvv, r> * r::ll<n1, s1>
		& vvv >= 0
		& n = n1 + 1
		& s = s1 + vvv
	inv n >= 0 & s >= 0;
*/

/* append two singly linked lists */

void append2(node x, node y)
  requires x::ll<n1, s1, S1> * y::ll<n2, s2, S2> & x!=null
  ensures x::ll<n, s, S> & n = n1 + n2 & s = s1 + s2 & S = union(S1,S2);
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

void append(node x, node y)
  requires x::ll<n1, s1, S1> * y::ll<n2, s2, S2> & n1>0
  ensures x::ll<n, s, S> & n = n1 + n2 & s = s1 + s2 & S = union(S1,S2);
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

/* return the first element of a singly linked list */

node ret_first(node x)

	requires x::ll<n, s, S> * y::ll<m, _, _> & n < m 
	ensures x::ll<n, s, S>;

{
	return x;
}

/* return the tail of a singly linked list */

node get_next(node x)

	requires x::ll<n, s, S> & n > 0
	ensures x::ll<1, s1, S1> * res::ll<n-1, s2, S2> & s = s1 + s2 & S = union(S1, S2); 

{
	//dprint;
	node tmp = x.next;
    //assume false;
	x.next = null;
	return tmp;
}

/* function to set the tail of a list */

void set_next(node x, node y)

	//requires x::ll<i,_,_> * y::ll<j, s1, S1> & i > 0
	requires x::node<v,_> * y::ll<j, s1, S1> & v>=0
	ensures x::ll<j+1, s, S> & s=s1+($ v) & S=union({($ v)}, S1); 

{
	x.next = y;
}

/* function to set null the tail of a list */

void set_null(node x)
	requires x::node<v, _> & v>=0
	ensures x::ll<1, ($ v), {($ v)}>;
{
	x.next = null;
}	

/* function to get the third element of a list */

node get_next_next(node x) 
	requires x::node<v1, n1> * n1::node<v2, n2> * n2::ll<n, s, S> & v1>=0 & v2>=0
	ensures res::ll<n, s, S>;
{
	return x.next.next;
}

/* function to insert a node in a singly linked list */

void insert(node x, int a)
	requires x::ll<n, s1, S1> & n > 0 & a>=0 
	ensures x::ll<n+1, s, S> & s = s1 + ($ a) & S = union(S1, {($ a)});
{
			//dprint;
      node tmp = null;
	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 

/* function to delete the a-th node in a singly linked list */

void delete(node x, int a)
	requires x::ll<n, _, _> & n > a & a > 0 
	ensures x::ll<n-1, _, _>;
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

node delete1(node x, int a)
	requires x::ll<n, s, S>  
	//ensures res::ll<n1, s1, S1> & (((($ a) notin S) | n=n1+1 & s=s1+($ a) & S=union(S1, {($ a)})) | n=n1 & s=s1 & S=S1);
	case {
		($ a) notin S -> ensures res::ll<n, s, S>;
		($ a) in S -> ensures res::ll<n1, s1, S1> & n=1+n1 & s=s1+($ a) & S=union(S1, {($ a)});
	}
{
	if (x == null)
	{
		//assume false;
		return x;
	}
	else {
		//assume false;
		if (x.val == a)
		{
			//assume false;
			return x.next;
		}
		else
		{
			//assume false;
			return new node(x.val, delete1(x.next, a));
		}
	}
}

/* function to create a singly linked list with n nodes */
node create_list(int n)
	requires n >= 0 
	ensures res::ll<n, s, S> & s = 0 & forall (x : (x notin S | x=0));
{
	node tmp;

	if (n == 0)
	{
		// assume false;
		return null;
	}
	else
	{    
		n  = n - 1;
        //    dprint;
		tmp = create_list(n);
        //    dprint;
		return new node (0, tmp);
	}		
}

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)
	requires xs::ll<n1, s1, S1> * ys::ll<n2, s2, S2> 
	ensures ys'::ll<n, s, S> & xs' = null & n=n1+n2 & s=s1+s2 & S=union(S1, S2);
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;

		//dprint;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		
		//dprint;
		reverse(xs, ys);
	}
}




