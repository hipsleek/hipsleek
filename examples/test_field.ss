data node {
	int val;
	node next;
}

sll<n> == self=null & n=0
	or self::node<_, r> * r::sll<n-1>
	inv n>=0;

void f(node x)
	requires x::sll<n> & n>10 ensures true;
{
	node tmp;
	tmp = x.next;
	tmp = x.next.next.next;
	int a = x.next.val;
	a = x.next.next.val;
}

void f1(node x)
	requires x::sll<n> & n>10 ensures true;
{
	node tmp;
	x.next = tmp;
	x.next.next = tmp;
	x.next.next.val = x.val;
}

void f3(node x)
	requires x::node<_, _> ensures true;
{
/*
	dprint;
	x.val = 20;
	dprint;
	x.val = 25;
	dprint;
*/
	int tmp;
	dprint;
	tmp = x.val;
	dprint;
	tmp = x.val;	
	dprint;
	tmp = x.val;	
	dprint;
/*
	x.val = 10;
	dprint;
	x.val = 15;
	dprint;
*/
}

void f4(node x)
	requires x::node<_,_> ensures true;
{
	bind x to (_, _) in {
		assert x' != null;
	}
}
