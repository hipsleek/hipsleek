data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;

void append(node x, node y)
  (
    requires x::ll<n> & x!=null //& n>0
    ensures x::lseg<y, n>;
    requires x::ll<n> & y=x & n>0
    ensures x::clist<n>;
   ) 
  (
    requires x::ll<n> * y::ll<m> & n>0
    ensures x::ll<e>& e=n+m;
   )
/*
    requires x::lseg<r, n> * r::node<b,null>
    ensures x::lseg<r,n> * r::node<b,y>;
*/
{
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
		append(x.next, y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

