/* singly linked lists */

/* representation of a node */
data node {
	int key;
	int val;
	node next
}

data intPair {
	int key;
	int val
}

ll<L1> == self=null & y=null & L1=[||]
       or self::node<k,v,r> * r::ll<L2> & L1=cons_p(k,v,L2);
       
/*sort by insertion method*/
node insertion_sort(node xs)
	requires xs::ll<L0>
	ensures res::ll<L1> & L1=inssort(L0) & stable (L0, L1);
{
	if (xs == null) {
		return xs;
	} else {
		intPair a = new intPair (xs.key, xs.val);
		return key_insert(insertion_sort(xs.next), a);
	}
}

/*insert the node to the correct position*/
node key_insert(node x, intPair a)
	requires x::ll<L0> * a::intPair<k,v>
	ensures res::ll<L1> * a::intPair<k,v> & L1 = kinsert(k,v,L0);
{
	if (x == null){
		return new node (a.key, a.val, null);
	} else {
		if (x.key < a.key) {
			return append_node (key_insert (x.next, a), x);
		} else {
			return append_val (x, a);
		}
	}
}

/*function to append the node with value a in a singly linked list*/
node append_val(node x, intPair a)
	requires x::ll<L1> * a::intPair<k,v>
	ensures res::ll<L2> * a::intPair<k,v> & L2=cons_p(k,v,L1);
{
	return new node (a.key, a.val, x);
}

/*function to append the node with value of head of x1 in a singly linked list*/
node append_node(node x, node x1)
	requires x::ll<L1> * x1::node<k,v,x2>
	ensures res::ll<L2> & L2=cons_p(k,v,L1);
{
	return new node (x1.key, x1.val, x);
}