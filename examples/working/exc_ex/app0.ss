data node {
	int val;
	node next;
}

list<> == self=null 
	or self::node<_, q> * q::list<>
	inv true;

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

void append(node x, node y)
	//requires x::list<> * y::list<> & x!=null
	//ensures x::list<>;
	requires x::ll<a> * y::ll<b>  & x!=null
	ensures x::ll<a+b>;
{
	if (x.next != null) {
		append(x.next, y);
		dprint;
		return;
	}
	else {
		x.next = y;
		dprint;
		return;
	}
}

