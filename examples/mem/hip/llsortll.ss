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

/* view for list segment */	
lseg<n,R,p> == self = p & R = {} & n = 0
	or self::node<_@L,q,_@A> * q::lseg<n-1,Rq,p> & R = union(Rq,{self})
	inv n>=0
	mem R->(node<@L,@M,@A>);
	
/* view for sorted list segment */
slseg<n,sm,lg,R,p> == self = p & R = {} & n = 0 & sm <= lg 
	or (exists qs,ql: self::node<qmin@L,_@A,q> * q::slseg<n-1,qs,ql,Rq,p> 
	& qmin <= qs & ql <= lg & sm <= qmin & R = union(Rq,{self}))
	inv n >= 0 & sm <= lg
	mem R->(node<@L,@A,@M>);
	
lemma self::sll<n,sm,lg,R> -> self::ll<n,R>;

lemma self::ll<n,R> <-> self::lseg<n,R,p>;

void overlaid_insert(ref node x, ref node s,int v)
requires x::ll<n,R> & s::sll<n,sm,lg,R>
ensures x'::ll<n+1,R1> & s'::sll<n+1,mi,ma,R1> & mi = min(v, sm) & ma = max(v, lg) &  R1 = union(R,{x}); 
{
node c = new node(v,null,null);
c.next = x;
x = c;
s = insert2(s,c);
}

void overlaid_delete(node x, node s, int v)
requires x::ll<n,R> & s::sll<n,sm,lg,R>
ensures x::ll<nres,R1> & s::sll<nres,mi,ma,R1> & mi = min(v, sm) & ma = max(v, lg) & (R1 subset R | R1 = R) & n-1 <= nres <= n;
/*
{
node c;
if(s == null) return;
c = delete(s,v);
s = c;
}
*/

void delete2(node x, node vn)
requires x::ll<n,R> * vn::node<_@L,_,_@A>
ensures x::ll<nres,R1> & n - 1 <= nres <= n; 
{
	if(x != null){
	if(x.next == vn)
	{
		x.next = vn.next;
		vn.next = null;
	}
	else delete2(x.next,vn);}
}

/* insert an element in a sorted list */
node insert(node x, int v)
requires x::sll<n, sm, lg, R>
ensures res::sll<n + 1, mi, ma, R1> & mi = min(v, sm) & ma = max(v, lg) & R subset R1;  
/*
{
	node tmp;

	if (x == null)
		return new node(v, null,null);
	else
	{
		if (v <= x.val)
			return new node(v, x,null);
		else
		{
			tmp = x.snext;
			x.snext = insert(tmp, v);
			return tmp;
		}
	}
}
*/

node insert2(node x, node vn)
	requires x::sll<n, sm, lg,R> *  vn::node<v@L,_@A,_>
	ensures res::sll<n+1, mi, ma, R1> & mi=min(v, sm) & ma=max(v, lg) & R1 = union(R,{vn});
{
	if (x==null) {
		vn.snext = null;
		return vn;
	}
	else if (vn.val <= x.val) {
		vn.snext = x;
		return vn;
	}
	else {
		x.snext = insert2(x.snext, vn);
		return x;
	}
}

/* delete a node from a sorted list */
node delete(node x, int v)
requires x::sll<n, xs, xl, R>
ensures res::sll<nres, sres, lres,R1> & sres >= xs & lres <= xl & n-1 <= nres <= n & (R1 subset R | R1 = R);
/*
{
	node tmp; 

	if (x != null)
		if (v < x.val)
			return x;
		else
			if (v == x.val)
				return x.snext;
			else
			{
				tmp = x.snext;
				x.snext = delete(tmp, v);
				return tmp;
			}
	else
		return null;
}
*/
/* get the tail of a sorted list */
node get_tail(node x)

	requires x::sll<n, xs, xl,R> & x != null
	ensures res::sll<n-1, sres, lres,R1> & sres >= xs & lres <= xl & R = union({x},R1); 

{
	return x.snext;
}

/* transform a normal singly linked list in a sorted list */
void insertion_sort(node x, ref node y)

	requires x::ll<n,Rll> * y::sll<m1, ys1, yl1,Rsll>
	ensures y'::sll<n + m1, _, _,R1> * x::ll<n,Rll> & R1 = union(Rsll,Rll) ;

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}

void id(int x)
	requires true ensures true;
{
	int n = 1; 

	n ++;
	id(n);
}
