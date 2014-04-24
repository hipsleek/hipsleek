data node {
	int val; 
	node next;	
}

ll<n> == 
	self = null & n = 0 or 
	self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

int fib (int n)
case {
	n<2 -> requires Term ensures res>=1;
	n>=2 -> requires Term[n] ensures res>=1;
}
{
	if (n < 2)
		return 1;
	else
		return fib(n - 1) + fib(n - 2);
}

int doSum (node x)
requires x::ll<n>@L & Term[n]
ensures res>=1;
{
	if (x == null)
		return 1;
	else
		return fib(x.val) + doSum(x.next);
}

node create (int n)
case {
	n<0 -> requires Loop ensures false;
	n>=0 -> requires Term[n] ensures res::ll<n>;
}
{
	if (n == 0)
		return null;
	else {
		int v = rand_int();
		return new node (v, create(n - 1));
	}
}

void main ()
requires Term
ensures true;
{
	int s = rand_int();
	node l = create(s * s);
	doSum(l);	
}

int rand_int ()
requires Term
ensures true;
