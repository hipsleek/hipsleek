data node {
	int val; 
	node next;	
}

sorted<"n":n,"t":t,"s":S> == self=null & ["n":n=0; "t":t=0; "s":S={}] or
		 //self::node<v,q> * q::sorted<n2,t2,S2> & ["n":n=n2+1; "t":t=t2+v & v>0; "s":S=union(S2, {v})]
		 self::node<v,q> * q::sorted<n2,t2,S2> & ["n":n=n2+1; "t":t=t2+2; "s":v>0 & S=union(S2, {v})]
		 inv true & ["n":n>=0; "t":t>=0];

node insert(node x, int a)
	requires x::sorted<n,t,S> & a>0
	//ensures res::sorted<n1,t1,S1> & ["n":n1=n+1; "t":t1=t+a; "s":S1=union(S,{a})];
	ensures res::sorted<n1,t1,S1> & ["n":n1=n+1; "t":t1=t+2; "s":S1=union(S,{a})];
{
	node tmp;
	node tmp1;
	if (x == null) {
		return new node(a, null);
	} else if (x.val >= a) {
		tmp1 = insert(x.next, a);
		tmp = new node (x.val, tmp1);
		return tmp;
	} else {
		tmp = new node(a, x);
		return tmp;
	}
}

node insert_last(node x, int a)
	//requires x::sorted2<n,t,S> & a>0 & ["s":forall (z:(z notin S | z <= a))]
	requires x::sorted<n,t,S> & a>0
	//ensures res::sorted<n1,t1,S1> & ["n":n1=n+1; "t":t1=t+a; "s":S1=union(S,{a})];
	ensures res::sorted<n1,t1,S1> & ["n":n1=n+1; "t":t1=t+2; "s":S1=union(S,{a})];
{
	node tmp;
	node tmp1;
	if (x == null)
		tmp = new node(a, null);
	else {
		tmp1 = insert_last(x.next, a);
		tmp = new node(x.val, tmp1);
	}
	return tmp;
}

node reverse(node x)
	requires x::sorted<n1,t1,S1>
	ensures res::sorted<n,t,S> & ["n":n=n1; "t":t=t1; "s":S=S1];
{
	node tmp;
	node tmp1;
	if (x == null) {
		//assume false;
		return null;
	}
	else {
		//assume false;
		tmp1 = reverse(x.next);
		tmp = insert_last(tmp1, x.val);
		return tmp;
	}
}

node insert_first(node x, int a)
	requires x::sorted<n,t,S> & a>0
	//ensures res::sorted<n1,t1,S1> & ["n":n1=n+1; "t":t1=t+a; "s":S1=union(S,{a})];
	ensures res::sorted<n1,t1,S1> & ["n":n1=n+1; "t":t1=t+2; "s":S1=union(S,{a})];
{
	return new node(a,x);
}

node copy(node x)
	requires x::sorted<n1,t1,S1>
	ensures res::sorted<n,t,S> & ["n":n=n1; "t":t=t1; "s":S=S1];
{
	node tmp;
	node tmp1;
	if (x == null) {
		return null;
	}
	else {
		tmp1 = copy(x.next);
		tmp = insert_first(tmp1, x.val);
		return tmp;
	}
}

node double_reverse(node x)
	requires x::sorted<n1,t1,S1>
	ensures res::sorted<n,t,S> & ["n":n=n1; "t":t=t1; "s":S=S1];
{
	node tmp;
	node tmp1;
	if (x == null) {
		//assume false;
		return null;
	}
	else {
		//assume false;
		tmp1 = double_reverse(x.next);
		tmp = insert_first(tmp1, x.val);
		return double_reverse(tmp);
	}
}


node merge(node x, node y)
	requires x::sorted<n1,t1,S1> * y::sorted<n2,t2,S2>
	ensures res::sorted<n,t,S> & ["n":n=n1+n2; "t":t=t1+t2; "s":S=union(S1,S2)];
{
	node tmp;
	node tmp1;
	if (y == null)
		return x;
	else {
		tmp1 = insert(x, y.val);
		tmp = merge(tmp1, y.next);
		return tmp;
	}
}

node delete(node x, int a)
	requires x::sorted<n1,t1,S1>
	//ensures res::sorted<n2,t2,S2> & ["n":n1=n2+1; "t":t1=t2+a; "s":S1=union(S2,{a})] or res::sorted<n3,t3,S3> & ["n":n3=n1; "t":t3=t1; "s":S3=S1];
	ensures res::sorted<n2,t2,S2> & ["n":n1=n2+1; "t":t1=t2+2; "s":S1=union(S2,{a})] or res::sorted<n3,t3,S3> & ["n":n3=n1; "t":t3=t1; "s":S3=S1];
{
	node tmp;
	node tmp1;
	if (x == null) {
		return null;
	}
	else {
		if (x.val == a) {
			return x.next;
		}
		else {
			tmp1 = delete(x.next, a);
			tmp = new node(x.val, tmp1);
			return tmp;
		}
	}
}


