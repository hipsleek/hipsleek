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

void overlaid_delete(node x, node s, int v)
requires x::ll<n,R> &* s::sll<n,sm,lg,R>
ensures x::ll<nres,R1> &* s::sll<nres,mi,ma,R1> & mi = min(v, sm) & ma = max(v, lg) & (R1 subset R | R1 = R) & n-1 <= nres <= n;
{
node c;
if(s == null) return;
//c = delete(s,v);
s = c;
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
node delete(node x, node vn)
requires x::sll<n, xs, xl, R> * vn::node<_@L,_@A,_> & vn in R & R != {}
ensures res::sll<nres, sres, lres,R1> & sres >= xs & lres <= xl & n-1 <= nres <= n & R = union(R1,{vn});
{
	node tmp; 
	int v = vn.val;
	if (x != null)
		if (v < x.val)
			return x;
		else
			if (v == x.val)
				return x.snext;
			else
			{
				tmp = x.snext;
				x.snext = delete(tmp, vn);
				return tmp;
			}
	else
		return null;
}
