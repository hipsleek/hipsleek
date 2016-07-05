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

/*ll1<S> == self = null & S = {}
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/* WORKING */
/*sll<sm, lg> == self = null & sm <= lg 
	or self::node<qmin, q> * q::sll<qs, ql> & qmin <= qs & lg >= ql & qmin >= sm & sm <= qs
	inv sm <= lg;*/

sll<n, sm, lg> == self = null & sm <= lg & n=0
	or self::node<qmin, q> * q::sll<n1, qs, ql> & n = n1+1 & qmin <= qs & lg >= ql & qmin >= sm & sm <= qs
	inv sm <= lg;


/*sll<sm> == self = null
	or self::node<qmin, q> * q::sll<qs> & qmin>=sm & qmin <= qs ;*/

/*sll1<S> == self=null & S={}
	or self::node<v, r> * r::sll1<S1>  & S=union(S1, {v}) & 
	forall (x: (x notin S1 | v <= x));*/

/* insert an element in a sorted list */
/*node insert(node x, int v)
	requires x::sll<sm, _> 
	ensures res::sll<mi, _> & mi = min(v, sm);
	/*requires x::sll<sm, lg> 
	ensures res::sll<mi, ma> & mi = min(v, sm) & ma = max(lg, v); */
{
	node tmp;
        node tmp_null = null;

	if (x == null)
		return new node(v, null);
	else
	{
		if (v <= x.val)
			return new node(v, x);
		else
		{
			//tmp = x.next;
			x.next = insert(x.next, v);	
			return x;
		
		}
	}
}*/

/*node insert1(node x, int v)
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
			x.next = insert1(tmp, v);	
			return x;
		}
	}
}*/

/* delete a node from a sorted list */
node delete(node x, int v)
	requires x::sll<n, xs, xl>
	ensures res::sll<n1, sres, lres> & /*(n = n1+1 | n = n1) &*/ sres >= xs & lres <= xl;

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
/*
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
}*/

/* get the tail of a sorted list */
/*node get_tail(node x)

	requires x::sll<n, xs, xl> & x != null
	ensures res::sll<n-1, sres, lres> & sres >= xs & lres <= xl; 

{
	return x.next;
}*/

/* transform a normal singly linked list in a sorted list */
/*void insertion_sort(node x, ref node y)
	/*requires x::ll<n> * y::sll<ys1, yl1>
	ensures y'::sll<_, _> * x::ll<n>;*/
	requires x::ll<n> * y::sll<ys1, _>
	ensures y'::sll<_, _> * x::ll<n>;
{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}*/


/*void insertion_sort1(node x, ref node y)
	requires x::ll1<S1> * y::sll1<S2>
	ensures y'::sll1<S> * x::ll1<S1> & S = union(S1, S2);

{
	if (x != null)
	{
		y = insert1(y, x.val);
		insertion_sort1(x.next, y);
	}
}
*/
void id(int x)
	requires true ensures true;
{
	int n = 1; 

	n ++;
	id(n);
}

