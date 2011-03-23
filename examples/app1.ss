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

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

ll_bag<B> == self = null & B = {} 
        or self::node<v, q> * q::ll_bag<B1> &  B = union({self}, B1)
        inv true;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;

sortl<s,l> == self=null & s<=l
	or self::node<v, q> * q::sortl<s2,l2> & s<=v<=s2 & l2<=l
	inv s<=l;

void append(node x, node y)
	//requires x::ll<n> * y::ll<m> & n>0
	//ensures x::ll<n+m>;
	//requires x::lseg<null,n> & n>0
	//ensures x::lseg<y, n>;
	requires x::ll_bag<B1> * y::ll_bag<B2> & x!=null 
	ensures x::ll_bag<union(B1,B2)> & x in B1;
	//requires x::lseg<null,n> & x=y & n>0
	//ensures x::clist<n>;
	//requires x::sortl<sx,lx> * y::sortl<sy,ly> & x!=null & lx<=sy
	//ensures x::sortl<sx,ly>;
{
        dprint;
        bool t;
        //t = (x.next!=null) ;
	if (x.next!=null) {
		dprint;
		append(x.next,y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

