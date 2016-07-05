data node {
	int val; 
	node next;	
}

sorted<n,t,S> == self=null & n=0 & t=0 & S={} or
		 self::node<v,q> * q::sorted<n2,t2,S2> & n=n2+1 & t=t2+v & v>0 & S=union(S2, {v}) & forall (x:(x notin S2 | v >= x))
		 //self::node<v,q> * q::sorted<n2,t2,S2> & n=n2+1 & t=t2+2 & v>0 & S=union(S2, {v}) & forall (x:(x notin S2 | v >= x))
		 inv n>=0 & t>=0;

sorted2<n,t,S> == self=null & n=0 & t=0 & S={} or
		 self::node<v,q> * q::sorted2<n2,t2,S2> & n=n2+1 & t=t2+v & v>0 & S=union(S2, {v}) & forall (x:(x notin S2 | v <= x))
		 //self::node<v,q> * q::sorted2<n2,t2,S2> & n=n2+1 & t=t2+2 & v>0 & S=union(S2, {v}) & forall (x:(x notin S2 | v <= x))
		 inv n>=0 & t>=0;

node insert(node x, int a)
	requires x::sorted<n,t,S> & a>0
	ensures res::sorted<n1,t1,S1> & n1=n+1 & t1=t+a & S1=union(S,{a});
	//ensures res::sorted<n1,t1,S1> & n1=n+1 & t1=t+2 & S1=union(S,{a});
{
	node tmp;
	node tmp1;
	if (x == null) {
		//assume false;
		return new node(a, null);
	} else if (x.val >= a) {
		//assume false;
		tmp1 = insert(x.next, a);
		tmp = new node (x.val, tmp1);
		return tmp;
	} else {
		//assume false;
		tmp = new node(a, x);
		return tmp;
	}
}

node insert_last(node x, int a)
	requires x::sorted2<n,t,S> & a>0 & forall (z:(z notin S | z <= a))
	ensures res::sorted2<n1,t1,S1> & n1=n+1 & t1=t+a & S1=union(S,{a});
	//ensures res::sorted2<n1,t1,S1> & n1=n+1 & t1=t+2 & S1=union(S,{a});
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

void id(node x)
	requires x=null
	ensures x::sorted2<n1,t1,S1> & n1=0 & t1=0 & S1={};
{
}

node reverse(node x)
	requires x::sorted<n1,t1,S1>
	ensures res::sorted2<n,t,S> & n=n1 & t=t1 & S=S1;
{
	node tmp;
	node tmp1;
	if (x == null) {
		//assume false;
		tmp = null;
		id(tmp);
		return tmp;
	}
	else {
		//assume false;
		tmp1 = reverse(x.next);
		tmp = insert_last(tmp1, x.val);
		return tmp;
	}
}

node insert_first(node x, int a)
	requires x::sorted<n,t,S> & a>0 & forall (z:(z notin S | a >= z))
	ensures res::sorted<n1,t1,S1> & n1=n+1 & t1=t+a & S1=union(S,{a});
	//ensures res::sorted<n1,t1,S1> & n1=n+1 & t1=t+2 & S1=union(S,{a});
{
	return new node(a,x);
}

node copy(node x)
	requires x::sorted<n1,t1,S1>
	ensures res::sorted<n,t,S> & n=n1 & t=t1 & S=S1;
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
	ensures res::sorted<n,t,S> & n=n1 & t=t1 & S=S1;
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
	ensures res::sorted<n,t,S> & n=n1+n2 & t=t1+t2 & S=union(S1,S2);
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
	ensures res::sorted<n2,t2,S2> & n1=n2+1 & t1=t2+a & S1=union(S2,{a}) or res::sorted<n3,t3,S3> & n3=n1 & t3=t1 & S3=S1;
	//ensures res::sorted<n2,t2,S2> & n1=n2+1 & t1=t2+2 & S1=union(S2,{a}) or res::sorted<n3,t3,S3> & n3=n1 & t3=t1 & S3=S1;
{
	node tmp;
	node tmp1;
	if (x == null) {
		//assume false;
		return null;
	}
	else {
		if (x.val == a) {
			//assume false;
			return x.next;
		}
		else {
			//assume false;
			tmp1 = delete(x.next, a);
			tmp = new node(x.val, tmp1);
			return tmp;
		}
	}
}


