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
	

int test1 (node x, node y) 
  requires x::node<v1,_>@I * y::node<v1,_>@I
  ensures res = v1+v2;
{
  return sum1(x,y);
}

int test2 (node x, node y) 
  requires x::node<v1,_>@I
  ensures res = v1+v1;
{
  return sum1(x,x);
}


/* usage of & */
int sum1(node x, node y)
requires (x::node<a, _>@I & y::node<b, _>@I) 
ensures res=a+b;
{ return x.val + y.val; dprint;}


int sum2(node x, node y)
requires (x::node<a, _>@I * y::node<b, _>@I) 
ensures res=a+b;
{ return x.val + y.val; dprint;}

