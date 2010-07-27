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

/*sort by quick method*/
node quick_sort(node x)
	requires x::ll<L0>
	ensures res::ll<L1> & quicksort(L0)=L1;
{
	return quick_sort_h(x, getLength(x));
}

node quick_sort_h(node x, int n)
	requires x::ll<L0> &  n >= 0
	ensures res::ll<L1> & quicksorth(L0, n)=L1;
{
	if (n == 0) {
		return null;
	} else {
		if (x == null) {
			return null;
		} else {
			intPair a = new intPair (x.key, x.val);
			node xl = getLeftPartition(a, x.next);
			node xr = getRightPartition(a, x.next);
			return append (quick_sort_h(xl, n-1), cons (quick_sort_h(xr, n-1), a));
		}
	}
}

int getLength(node x)
	requires x::ll<L0>
	ensures x::ll<L0> & res = len(L0);
{
	if (x == null){
		return 0;
	} else {
		return (getLength(x.next) + 1);
	}
}

node getLeftPartition (intPair a, node x)
    requires x::ll<L0> * a::intPair<k,v> 
    ensures res::ll<L1> * x::ll<L0> * a::intPair<k,v> & L1=fst(partition(k,v,L0));
{
    if (x == null){
    	return null;
    } else {
    	node tmp = getLeftPartition (a, x.next);
    	if (x.key < a.key) {
    		return new node (x.key, x.val, tmp);
    	} else {
    		return tmp;
    	}
    }
}

node getRightPartition (intPair a, node x)
    requires x::ll<L0> * a::intPair<k,v> 
    ensures res::ll<L1> * x::ll<L0> * a::intPair<k,v> & L1=snd(partition(k,v,L0));
{
    if (x == null){
    	return null;
    } else {
    	node tmp = getRightPartition (a, x.next);
    	if (x.key < a.key) {
    		return tmp;
    	} else {
    		return new node (x.key, x.val, tmp);
    	}
    }
}


/* append two singly linked lists */
node append(node x, node y)
	requires x::ll<L1> * y::ll<L2>
	ensures res::ll<L> & L = app(L1, L2) & len(L) = len(L1) + len(L2);
{
	if (x == null){
		return y;
	} else {
		return new node (x.key, x.val, append (x.next, y));
	}
}

/*function to append the node with value a in a singly linked list*/
node cons(node x, intPair a)
	requires x::ll<L1> * a::intPair<k,v>
	ensures res::ll<L2> * a::intPair<k,v> & L2=cons_p(k,v,L1);
{
	return new node (a.key, a.val, x);
}