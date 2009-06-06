data node2 {
	int val;
	node2 prev;
	node2 next;
}

dll<p,n> == self=null & n=0
	or self::node2<_,p,q> * q::dll<self,n-1>
	inv n>=0;

void append(node2 x, node2 y)
	requires x::dll<p,n> * y::dll<_,m> & x!=null 
	ensures x::dll<p,n+m>;
{
	if (x.next != null) {
		append(x.next,y);
		return;
	}
	else {
		x.next = y;
                if (y !=null) y.prev=x;
		return;
	}
}

