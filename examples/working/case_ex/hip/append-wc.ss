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
  
    case {
    x=y -> requires x::ll<n> & n>0 ensures x::clist<n>;
    x!=y -> requires x::ll<n> & n>0 ensures x::lseg<y, n>;}
{
	if (x.next != null) {
		append(x.next, y);
		dprint;
    assume false;
	}
	else x.next = y;
}
