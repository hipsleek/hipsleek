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

/* function to insert an element in a sorted list */
node insert(node x, int v)
	requires x::sll1<S>
	ensures res::sll1<S1> & S1 = union(S, {v}); 

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
			x.next = insert(tmp, v);	
			return x;
		}
	}
}

/* delete a node from a sorted list */
node delete(node x, int v)
	requires x::sll1<S>
	ensures res::sll1<S1> & (v notin S & S = S1 | S = union(S1, {v}));

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
				x.next = delete(tmp, v);
				return x;
			}
	else
		return null;
}

/* insertion sort */
void insertion_sort(node x, ref node y)
	requires x::ll1<S1> * y::sll1<S2>
	ensures y'::sll1<S> * x::ll1<S1> & S = union(S1, S2);

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}


