data node {
	int val;
	node next;
}

data node2 {
	int val1;
	bool val2;
	node2 p1;
	node2 p2;
}

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<m> & n=m+1 inv n>=0;


ll_client<n> == self::ll<n>;

ll_client1<m> == self::ll<m> & m<10;

v2<n> == self::node<_, n>;

node id(node x)
	requires x::ll<m> ensures res::ll<m> & res=x;
	requires x::ll<10> ensures res::ll<a> & a>0;
{
	return x;
}

node test1() 
	requires true ensures res::ll<0>;
{
	return null;
}

node test2()
	requires true ensures res::ll<1>;
{
	node x = new node(10, null);
	return x;
}

node test3()
	requires true ensures res::ll<1>;
{
	return new node(2, null);
}

node test4(node x)
	requires x::ll<n> ensures res::ll<n+1>;
{
	return new node(0, x);
}


void test5(node x, node y)
	requires x::node<_, _> * y::ll<n> ensures x::ll<n+1>;
{
	x.next = y;
}

node test6(node x)
	requires x::ll<n> ensures res::ll<n+1>;
{
	node tmp = new node(0, null);
	tmp.next = x;
	return tmp;
}

void test7(node x)
	requires x::node<_, _> ensures true;
{
	x.next = null;
	dprint;
}

node insert(node x, int a)
	requires x::ll<n> ensures res::ll<n+1>;
	//requires x::ll<n> & x!=null ensures res::ll<n+1>;
	//requires x=null ensures res::ll<1>;
{
	if (x==null) return new node(a, null); // return new node(a, x);
	else {
		return new node(a, x);
	}
}
