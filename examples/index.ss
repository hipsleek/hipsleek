data lnode {
	int key;
	lnode prev;
	lnode next;
}


data tnode {
	int key;
	lnode ptr;
	
	tnode left;
	tnode right;
}

/*
doubly linked list storing data items
*/
dll0<n, p> == self = null & n = 0
	or self::lnode<_, p, q> * q::dll0<n-1, self>
	inv n>=0;

//dll1<p, AB, CB> == self = null & AB = {} & CB = {}
//	or self::lnode<v, p, q> * q::dll1<self, AB1, CB1> & AB = union(AB1, {self}) & CB = union(CB1, {v});

/*
index with pointers to the list.

n keeps track of the number of nodes st ptr != null
*/
ind0<n, sm, lg> == self=null & n=0 & sm<=lg
	or self::tnode<k, p, l, r> * l::ind0<n1, sm, llg> * r::ind0<n2, rsm, lg> 
		& sm <= llg <= k <= rsm <= lg & (p != null & n = n1 + n2 + 1 | p = null & n = n1 + n2)
	inv n >= 0;


/* insert a node in a bst */
tnode insert(tnode x, lnode p)
	requires x::ind0<n, sm, lg> * p::lnode<k, _, _>
	ensures res::ind0<n+1, mi, ma> & mi = min(sm, k) & ma = max(lg, k);
{
	tnode tmp;

	if (x == null)
		return new tnode(p.key, p, null, null);
	else {
		if (p.key <= x.key) {
			x.left = insert(x.left, p);
		}
		else { 
			x.right = insert(x.right, p);
		}
		return x;
	}
}

/*
build the index tree from a doubly-linked list of nodes
*/
tnode build_tree(lnode input)
	requires input::dll0<n, _>
	ensures res::ind0<n, _, _> * input::dll0<n, _>;
{
	if (input == null) return null;

	if (input.next != null) {
		tnode tmp2 = build_tree(input.next);
		tmp2 = insert(tmp2, input);
		return tmp2;
	}
	else {
		tnode tmp1 = new tnode(input.key, input, null, null);
		return tmp1;
	}
}

/*
look up an lnode using the index.

lookup needs to associate res with dll0
*/
lnode lookup(tnode ind, int key)
	requires ind::ind0<n, sm, lg>
	ensures ind::ind0<n, sm, lg>;
{
	if (ind == null) return null;
	
	if (ind.key == key) return ind.ptr;

	if (key < ind.key) return lookup(ind.left, key);

	return lookup(ind.right, key);
}

/*
remove an element from the structure. 
This is going to be challenging.
*/
void remove(ref tnode ind, ref lnode input, int key)
	requires ind::ind0<n, sm, lg> * input::dll0<n, p>
	ensures ind'::ind0<_,_,_> * input'::dll0<_,_>;
{
	lnode tmp = lookup(ind, key);
	if (tmp != null) {
		// found the node
		if (tmp.prev != null)
			tmp.prev.next = tmp.next;
		if (tmp.next != null)
			tmp.next.prev = tmp.prev;
	}
}

/*
build an indexing tree from a list of objects. Then use it for
searching the list.

specifications: the set of hanging pointers from ind is the same as
the set of nodes in objs. The returned value belongs to this set if
the key is found. Otherwise it returns null.

Above spec should work in a function that builds the tree, then uses
it for indexing. lookup function should only work on the tree.
*/
void app1(lnode input) 
	requires objs::dll0<n, p>
	ensures true;
//	requires objs::dll1<p, AB, CB>
//	ensures true;
{
	tnode ind = build_tree(input);

	
	int k; // k = ....

	lnode result = lookup(ind, k);

	// assert: if k in objs.content then result in objs.
}

