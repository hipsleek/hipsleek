/* sorted lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll1<S> == self = null & S = {}
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});

sll1<S> == self=null & S={}
	or self::node<v, r> * r::sll1<S1>  & S=union(S1, {v}) & 
	forall (x: (x notin S1 | v <= x));

//relation A(bag S, bag S1, int v).

/* insert an element in a sorted list */
node insert1(node x, int v)
	requires x::sll1<S>
	ensures res::sll1<S1> /*& A(S,S1,v);*/ S1 = union(S, {v}); 

{
	node tmp;
        node tmp_null = null;

	if (x == null)
		return new node(v, tmp_null);
	else
	{
		if (v <= x.val)
			return new node(v, x);
		else
		{
			tmp = x.next;
			x.next = insert1(tmp, v);	
			return x;
		}
	}
}

/* delete a node from a sorted list */
node delete1(node x, int v)
	requires x::sll1<S>
	ensures res::sll1<S1> & (v notin S | S = union(S1, {v})) or S = S1;

{
	node tmp; 

	if (x != null)
		if (v < x.val)
			return x;
		else
 			if (v == x.val)
				return x.next;
			else
			{
				tmp = x.next;
				x.next = delete1(tmp, v);
				return x;
			}
	else
		return null;
}

void insertion_sort1(node x, ref node y)
	requires x::ll1<S1> * y::sll1<S2>
	ensures y'::sll1<S> * x::ll1<S1> & S = union(S1, S2);

{
	if (x != null)
	{
		y = insert1(y, x.val);
		insertion_sort1(x.next, y);
	}
}


