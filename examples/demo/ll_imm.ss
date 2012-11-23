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

int length (node x) 
requires x::ll<n>
ensures x::ll<n> & res = n;
//requires x::ll<n>@I
//ensures res = n;
{
 if (x==null) return 0;
    else return 1+length(x.next);
}

void append(node x, node y)
  requires x::lseg<p,n>@I * p::node<v,null>
  ensures p::node<v,y>;
//  requires x::lseg<p,n> * p::node<v,null>
//  ensures x::lseg<p,n> * p::node<v,y>;

{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}


/* usage of & */
int sumN(node x, node y)
requires (x::node<a, _>@I & y::node<b, _>@I) 
ensures res=a+b;
{ return x.val + y.val; dprint;}

