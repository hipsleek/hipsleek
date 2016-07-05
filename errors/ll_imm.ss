/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

/* view for a singly linked list */

/*
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;
*/


lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;




/* function to get the third element of a list */
node get_next_next(node x) 
	//requires x::ll<n>@I & n > 1
	//ensures res::ll<n-2>@I;
	//requires x::node<_,q>@I*q::node<_,r>@I //ll<n>@I & n > 1
	//ensures res=r;
	requires x::lseg<r,nn>@L & nn=2
	ensures res=r;

{
        node t = x.next;
        dprint;
        t=t.next;
        dprint;
        //assume false;
        //assert t'=r;
	return t;
}




