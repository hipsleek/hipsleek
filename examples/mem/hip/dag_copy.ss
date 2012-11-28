data node {
	node copy; 
	node left;
	node right;	
}
	
ddag<y,M> ==  self = null & self = y & M = {}
	or self::node<y,l@I,r@I> * y::node<_,yl@I,yr@I> * l::ddag<yl,Ml> & r::ddag<yr,Mr> 
		& M = union({self},Ml,Mr) & y notin M
	inv true
	mem M->(node<@M,@I,@I>);
	
icdag<v,M> ==  self = null & M = {}
	or self::node<c@I,l@I,r@I> * c::node<_@I,_@I,_@I> * l::icdag<0,Ml> & r::icdag<0,Mr> & M = union({self},Ml,Mr) & v = 0
	or self::node<null,l@I,r@I> * l::icdag<_,Ml> & r::icdag<_,Mr> & M = union({self},Ml,Mr) & v = 1
	inv true
	mem M->(node<@I,@I,@I> & v = 0 ; node<@M,@I,@I> & v = 1 );

lemma self::ddag<c,M> <-> self::icdag<0,M>;

node copy_dag(node x)
requires x::icdag<_,M>
ensures x::ddag<y,M> & res = y;
{
	node l,r,ll,rr,y;
	if(x==null) return null;
	if(x.copy != null)
		return x.copy;
	l = x.left;
	r = x.right;
	ll = copy_dag(l);
	rr = copy_dag(r);
	y = new node(null,ll,rr);
	x.copy = y;
	return x.copy;
}
