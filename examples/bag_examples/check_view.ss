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

ll<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll<m, S1> & n=m+1 & S=union(S1, {v});


ll_client<n, S> == self::ll<n, S>;

ll_client1<m, S> == self::ll<m, S> & m<10;

v2<n> == self::node<_, n>;

ll1<n> == self=null & n=0
	or self::node<v, r>* r::ll1<m> & n=m+1 & n>=1;

ll2<S> == self=null & S={}
	or self::node<v, r> * r::ll2<S1>  & S=union(S1, {v});


/*node id(node x)
	requires x::ll<m, S> ensures res::ll<m, S> & res=x;
	requires x::ll<10, S> ensures res::ll<a, S> & a>0;
{
	return x;
}

node test1() 
	requires true ensures res::ll<0, S> & S={};
{
	return null;
}

node test2()
	requires true ensures res::ll<1, S> & S = {10};
{
	node x = new node(10, null);
	return x;
}

node test3()
	requires true ensures res::ll<1, S> & S = {2};
{
	return new node(2, null);
}

node test4(node x)
	requires x::ll<n, S> ensures res::ll<n+1, S1> & S1 = union(S, {0});
{
	return new node(0, x);
}


void test5(node x, node y)
	requires x::node<_, _> * y::ll<n, S> ensures x::ll<n+1, S1>;
{
	x.next = y;
}

node test6(node x)
	requires x::ll<n, S> ensures res::ll<n+1, S1> & S1=union(S, {0});
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
	requires x::ll<n, S> ensures res::ll<n+1, S1> & S1 = union(S, {a});
{
	if (x==null) return new node(a, null); // return new node(a, x);
	else {
		return new node(a, x);
	}
}

node id(node x)
	requires x::ll<m, S> ensures res::ll<m, S> & res=x;
	requires x::ll<10, S> ensures res::ll<a, S> & a>0;
{
	return x;
}*/

node test1() 
	requires true ensures res::ll2<S> & S={};
{
	return null;
}

node test2()
	requires true ensures res::ll2<S> & S = {10};
{
	node x = new node(10, null);
	return x;
}

node test3()
	requires true ensures res::ll2<S> & S = {2};
{
	return new node(2, null);
}

node test4(node x)
	requires x::ll2<S> ensures res::ll2<S1> & S1 = union(S, {0});
{
	return new node(0, x);
}


void test5(node x, node y)
	requires x::node<_, _> * y::ll2<S> ensures x::ll2<S1>;
{
	x.next = y;
}

node test6(node x)
	requires x::ll2<S> ensures res::ll2<S1> & S1=union(S, {0});
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
	requires x::ll2<S> ensures res::ll2<S1> & S1 = union(S, {a});
{
	if (x==null) return new node(a, null); // return new node(a, x);
	else {
		return new node(a, x);
	}
}

