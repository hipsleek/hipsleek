data node {
        int val;  
        node next;
}

ll<n> == self=null & n = 0
        or self::node<_, r> * r::ll<n-1>
	inv n >= 0;

lseg<p, n> == self=p & n = 0
        or self::node<_, r> * r::lseg<p, n-1>
	inv n >= 0;

clist<n> == self::node<_, p> * p::lseg<self, n-1>
	inv n >= 1;

lemma self::lseg<p, n> <-> self::lseg<q, n1> * q::lseg<p, n2> & n=n1+n2;

lemma self::lseg<p, n> <-> self::lseg<q, n-1> * q::node<_, p>;

void append(node x, node y) 
//requires x::ll<n1> * y::ll<n2> & n1>0 //& x=y
//ensures x::ll<n1+n2>;
//requires x::ll<n>  & n>0 & x=y
//ensures x::clist<n>;
requires x::ll<n> & n>0  
ensures x::lseg<y, n>;
{
	if(x.next != null) append(x.next, y);
	else {x.next = y; assert n=1; dprint; assume false;}
}
  
