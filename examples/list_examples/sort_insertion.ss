/* sorted lists */

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
	ensures res::ll<L1> & L1=selsort(L0) & stable (L0, L1); //& perm (L0, L1) & sorted (L1);
{
    if (xs != null) {
        intPair min_node = minimum (xs);
        node xs_next = delete_val (xs, min_node);
        node ins_next = insertion_sort (xs_next);
        return append_val (ins_next, min_node);
    } else {
    	return null;
    }
}

/*minimum of list*/
intPair minimum(node x)
    requires x::ll<L> & len(L) > 0
    ensures x::ll<L> * res::intPair<k,v> & f_oc(k,L,v) & k=fst(listmin(head(L), tail(L))); // & v=snd(listmin(head(L), tail(L)));
{
	intPair tmp = new intPair(x.key, x.val);
	if (x.next != null) {
		intPair m = minimum (x.next);
    	if (m.key < tmp.key) {
    		tmp = m;
	    }
    }
	return tmp;
}

/*function to delete the node with value a in a singly linked list*/
node delete_val(node x, intPair a)
	requires x::ll<L1> * a::intPair<k,v> & f_oc(k,L1,v) & len(L1)>0
	ensures res::ll<L2> * a::intPair<k,v> & L2=remove(k,v,L1);
{
	if (x.key == a.key)
	    return x.next;
	else
	    return new node(x.key, x.val, delete_val(x.next, a));
}

/*function to append the node with value a in a singly linked list*/
node append_val(node x, intPair a)
	requires x::ll<L1> * a::intPair<k,v>
	ensures res::ll<L2> * a::intPair<k,v> & L2=cons_p(k,v,L1);
{
	return new node (a.key, a.val, x);
}