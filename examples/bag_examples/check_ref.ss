data node {
	int val;
	node next;
}

ll<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll<m, S1> & n=m+1 & S=union(S1, {v});
	
ll1<n> == self=null & n=0
	or self::node<v, r>* r::ll1<m> & n=m+1 & n>=1;

ll2<S> == self=null & S={}
	or self::node<v, r> * r::ll2<S1>  & S=union(S1, {v});
	
void test(ref node x)
	requires x::ll<n, S> ensures x'=null;
{
	if (x!=null) {
		x = x.next;
		test(x);
	}
}

void test1(ref node x)
	requires x::ll1<n> ensures x'=null;
{
	if (x!=null) {
		x = x.next;
		test1(x);
	}
}

void test2(ref node x)
	requires x::ll2<S> ensures x'=null;
{
	if (x!=null) {
		x = x.next;
		test2(x);
	}
}