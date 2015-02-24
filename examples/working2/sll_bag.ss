/* sorted lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1>
	inv n >= 0;

ll1<S> == self = null & S = {}
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});


/* view for a sorted list */
sll<n, sm, lg> == self = null & n = 0 //& sm <= lg 
	or self::node<qmin, q> * q::sll<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin  
	inv n >= 0;// & sm <= lg;

sll1<S> == self = null & S = {}
	or self::node<v, r> * r::sll1<S1>  & S = union(S1, {v}) & 
	forall (x: (x notin S1 | v <= x)); // | is "or", not bounded quantification


/* insert a number into a sorted list */
node insert_int1(node x, int v)
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
			x.next = insert_int1(tmp, v);	
			return x;
		}
	}
}


/* delete a node from a sorted list */
node delete1(node x, int v)
	requires x::sll1<S>
	ensures res::sll1<S1> & (v notin S | S = union(S1, {v})) 
	& (v in S | S = S1);

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

node insert1(node x, node vn)
	requires x::sll1<S> * vn::node<v, _>
	ensures res::sll1<S1> & S1 = union(S, {v}); 
{
	if (x==null) {
		vn.next = null;
		return vn;
	}
	else if (vn.val <= x.val) { 	// corect code
	//else if (vn.val >= x.val) { 	// buggy code
		vn.next = x;
		return vn;
	}
	else {
		x.next = insert1(x.next, vn);
		return x;
	}
}

/* transform a normal singly linked list in a sorted list */
node insertion_sort1(node x)
	requires x::ll1<S> & S != {}
	ensures res::sll1<S>;
{
	if (x.next != null) {
		x.next = insertion_sort1(x.next);
		return insert1(x.next, x);
	}
	else { 
		return x;
	}
}
