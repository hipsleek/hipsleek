/* linked list and sorted linked list */

/* representation of a node */

data node {
	int val; 
	node next;
	node snext;	
}

/* view for a linked list */

ll<n,R> == self = null & R = {} & n = 0
		or self::node<_@L,p,_@A> * p::ll<n-1,Rp> & R = union(Rp,{self})
		inv n >= 0
		mem R->(node<@L,@M,@A>);

/* view for a sorted list */

sll<n, sm, lg, R> == self = null & n = 0 & sm <= lg & R = {}
	or (exists qs,ql: self::node<qmin@L,_@A,q> * q::sll<n-1, qs, ql, Rq> 
	& qmin <= qs & ql <= lg & sm <= qmin & R = union(Rq,{self}))
	inv n >= 0 & sm <= lg
	mem R->(node<@L,@A,@M>);

void overlaid_delete1(node x, node s, node vn)
requires vn::node<_@L,_,_> * x::ll<n,R> &* s::sll<n,sm,lg,R> & vn in R
ensures x::ll<nxres,Rx> &* s::sll<nres, sres, lres, Rs> & sres >= xs & lres <= xl & n-1 <= nres <= n 
	& n-1 <= nxres <= n & R = union(Rs,{vn}) & R  = union(Rx,{vn});
{
delete2(x,vn);
//dprint;
delete3(s,vn);
//dprint;
}

void delete3(node x, node vn)
requires x::sll<n, xs, xl, R> * vn::node<v@L,_@A,_> & vn in R
ensures x::sll<nres, sres, lres, R1> & sres >= xs & lres <= xl & n-1 <= nres <= n & R = union(R1,{vn});
{
	if(x != null){
	if(x.snext == vn)
	{
		x.snext = vn.snext;
		vn.snext = null;
	}
	else delete3(x.snext,vn);}
}

void delete2(node x, node vn)
requires x::ll<n,R> * vn::node<_@L,_,_@A> & vn in R
ensures x::ll<nres,R1> & n - 1 <= nres <= n & R = union(R1,{vn}); 
{
	if(x != null){
	if(x.next == vn)
	{
		x.next = vn.next;
		vn.next = null;
	}
	else delete2(x.next,vn);}
}

/* delete a node from a sorted list */
node delete(node x, node vn,int v)
requires x::sll<n, xs, xl, R> * vn::node<v@L,_@A,_> & vn in R
ensures res::sll<nres, sres, lres, R1> & sres >= xs & lres <= xl & n-1 <= nres <= n & R = union(R1,{vn});
{
	node tmp; 
//	int v = vn.val;
	if (x != null)
		if (v < x.val)
			return x;
		else
			if (v == x.val)
				return x.snext;
			else
			{
				tmp = x.snext;
				x.snext = delete(tmp, vn,v);
				return tmp;
			}
	else
		return null;
}
