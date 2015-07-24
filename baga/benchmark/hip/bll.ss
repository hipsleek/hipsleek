/* bounded lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for bounded lists */
bndl<n, sm, bg> == self = null & n = 0 & sm <= bg
	or self::node<d,p> * p::bndl<n-1, sm, bg> & sm <= d & d <= bg  
	inv sm <= bg & n >= 0;

/* insert a node as the first one in a bounded list */
node insert(node x, int v)

	requires x::bndl<n, sm, bg> & sm <= v & v <= bg 
	ensures res::bndl<n+1, sm, bg>;

{
	return new node(v,x);
}

/* delete a node from a bounded list */
node delete(node x)

	requires x::bndl<n,sm,bg> & x != null
	ensures res::bndl<n-1, sm, bg>;

{
	return x.next;
}

