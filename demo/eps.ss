/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

node get_next(node x) 
	requires x::ll<1>
	ensures res=null;
{
        node t = x.next;
        assert t'=null;
	return t;
}


node get_next_next(node x) 
	requires x::lseg<r,2>
	ensures res=r;
{
        node t = x.next.next;
	return t;
}
