data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

sortl<n,mi,mx> == self::node<mi,null> & mi=mx & n=1
	or self::node<mi, q> * q::sortl<n-1,k,mx> & mi<=k
	inv n>=1 & mi<=mx;

void append(node x, node y)
	requires x::ll<n> * y::ll<m> & x!=null 
	ensures x::ll<n+m>;
	requires x::sortl<n,sx,lx> * y::sortl<m,sy,ly> & lx<=sy
	ensures x::sortl<n+m,sx,ly>;
{
	if (x.next != null) {
		append(x.next,y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

