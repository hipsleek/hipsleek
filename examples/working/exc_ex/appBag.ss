data node {
	int val;
	node next;
}

ll_bag<B> == self = null & B = {} 
        or self::node<v, q> * q::ll_bag<B1> &  B = union({self}, B1)
        inv true;

void append(node x, node y)
	requires x::ll_bag<B1> * y::ll_bag<B2> & x!=null 
	ensures x::ll_bag<union(B1,B2)> & x in B1;
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

