data node {
	int val;
	node next;
}

ll<n> == self = null & n = 0
      or self::node<_, q> * q::ll<n-1>
      inv n>=0;

int length(node x)
/*
requires x::ll<n>
ensures x::ll<n> & res=n;
*/
requires x::ll<n>@I
ensures res=n;

{
	if (x == null) return 0;
	else return 1 + length(x.next); 
}

int sum(node x, node y)
requires (x::node<a,_>@I & y::node<b,_>@I)
ensures res=a+b;
{
	return x.val + y.val;
}

