data node {
	int val; 
	node next;	
}

ll<n> == 
	self = null & n = 0 or 
	self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

int fact (int n)
case {
	n<0 -> requires Term ensures true;
	n>=0 -> requires Term[n] ensures true;
}
{
	if (n < 0)
		return 1;
	else
		return n * fact(n - 1);
}

int doSum (node x)
requires x::ll<n>@L & Term[n]
ensures true;
{
	if (x == null)
		return 0;
	else
		return fact(x.val) + doSum(x.next);
}
