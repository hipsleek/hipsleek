data node {
	int val;
	node next;
}

ll<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll<m, S1> & n=m+1   & S=union(S1, {v});

ll1<n> == self=null & n=0
	or self::node<v, r>* r::ll1<m> & n=m+1 & n>=1;

ll2<S> == self=null & S={}
	or self::node<v, r> * r::ll2<S1>  & S=union(S1, {v});


node append(node x, node y)
 requires x::ll<n, S3> * y::ll<m, S4> 
 ensures res::ll<n+m, S5> & S5 = union(S3, S4);
{
	node z;
	if (x==null) return y;
	else { 
		assume false;
		return new node(x.val, append(x.next, y));
	  //bind x to (v1,x1) in {
	  //z = new node(v1, append(x1, y));
		//};
		//return z;
	}
}	

node append1(node x, node y)
 requires x::ll1<n> * y::ll1<m> 
 ensures res::ll1<n+m>;
{
	node z;
	if (x==null) return y;
	else { 
		assume false;
		return new node(x.val, append1(x.next, y));
	}
}

node append2(node x, node y)
 requires x::ll2<S3> * y::ll2<S4> 
 ensures res::ll2<S5> & S5 = union(S3, S4);
{
	node z;
	if (x==null) return y;
	else { 
		assume false;
		return new node(x.val, append(x.next, y));
	  //bind x to (v1,x1) in {
	  //z = new node(v1, append(x1, y));
		//};
		//return z;
	}
}

/* verifying commutativity:*/
node comm(node x, node y) 
 requires  x::ll<n, S1> * y::ll<m, S2> 
 ensures res::ll<n+m, S3> & S3=union(S1,S2);
{
  return append(y,x);
}

node comm1(node x, node y) 
 requires  x::ll1<n> * y::ll1<m> 
 ensures res::ll1<n+m>;
{
  return append1(y,x);
}

node comm2(node x, node y) 
 requires  x::ll2<S1> * y::ll2<S2> 
 ensures res::ll2<S3> & S3=union(S1,S2);
{
  return append2(y,x);
}

	
node tail(node x)
 requires x::ll<n, S3> & S3!={}
 ensures res::ll<n-1, S4> & S4 subset S3;
{
	return x.next;
}

node tail1(node x)
 requires x::ll1<n> & n>0
 ensures res::ll1<n-1>;
{
	return x.next;
}

node tail2(node x)
 requires x::ll2<S3> & S3!={}
 ensures res::ll2<S4> & S4 subset S3;
{
	return x.next;
}



int head(node x) 
  requires x::ll<n, S3> & S3!={} & n>0  ensures x::ll<n, S3> & res in S3;
{
  return x.val;
} 

int head1(node x) 
  requires x::ll1<n> & n>0 ensures x::ll1<n>;
{
	//bind x to (x1, x2) in {
  	return x.val;
  //}
}

int head2(node x) 
  requires x::ll2<S3> & S3!={} ensures x::ll2<S3> & res in S3;
{
  return x.val;
}

/*node head_(node x) 
  requires x::ll<n, S3> & S3!={} 
  ensures res::ll<1, S4> & S4 subset S3;
  // x::LL<S1> *--> res::LL<S2> & subset(S2,S1)  // not subseteq
  // x::LL<S1> *--> res::LL<S2> & S1=union(S2,S1)
{
  return new node(x.val, null);
} 
*/
 
node insert(node x, int a)
	requires x::ll<n, S> ensures res::ll<n+1, S1> & S1 = union(S, {a});
{
	return new node(a, x);
	
}

node insert1(node x, int a)
	requires x::ll1<n> ensures res::ll1<n+1>;
{
	return new node(a, x);
	
}

node insert2(node x, int a)
	requires x::ll2<S> ensures res::ll2<S1> & S1 = union(S, {a});
{
	return new node(a, x);
	
}

/* insert into the second position of a linked list */
/*node insert2(node x, int a)
	requires x::ll<n, S> & n>0 
	ensures res::ll<n+1, S1> & S1 = union(S, {a});
{
		return new node(x.val, new node(a, x.next));
}
*/	
/* recursive insert that goes by sortedness */
/*node insert3(node x, int a)
	requires x::ll<n, S> ensures res::ll<n+1, S1> & S1 = union(S, {a});
{
	if (x==null) return new node(a, null); // return new node(a, x);
	else {
		if (a > x.val) return new node(x.val, insert3(x.next, a));
		else return new node(a, x);
	}
}
*/
	
int length(node x)
	requires x::ll<n, S> 
	ensures x::ll<n, S> & res=n;
{
	if (x==null) return 0;
	else return 1 + length(x.next);
}

int length1(node x)
	requires x::ll1<n> 
	ensures x::ll1<n> & res=n;
{
	if (x==null) return 0;
	else return 1 + length1(x.next);
}

int length2(node x)
	requires x::ll2<S> 
	ensures x::ll2<S>;
{
	if (x==null) return 0;
	else return 1 + length2(x.next);
}

node fold()
	requires true
	ensures res::ll<n, S> & n>0 & S={0};
{
	node x;
	x = new node(0,null);
	return x;
}

node fold1()
	requires true
	ensures res::ll1<1>;
{
	node x;
	x = new node(0,null);
	return x;
}

node fold2()
	requires true
	ensures res::ll2<S> & S={0};
{
	node x;
	x = new node(0,null);
	return x;
}


int exist(node x, int a)
 requires x::ll<n, S1> 
 ensures res = 1 & a in S1 or res=0 & a notin S1;
{
	if (x==null) return 0;
	else {
		if (x.val==a) return 1;
		else return exist(x.next, a);
	}
}	

int exist1(node x, int a)
 requires x::ll1<n> 
 ensures x::ll1<n>;
{
	if (x==null) return 0;
	else {
		if (x.val==a) return 1;
		else return exist1(x.next, a);
	}
}	

int exist2(node x, int a)
 requires x::ll2<S1> 
 ensures res = 1 & a in S1 or res=0 & a notin S1;
{
	if (x==null) return 0;
	else {
		if (x.val==a) return 1;
		else return exist2(x.next, a);
	}
}	


void part(int a, node x, ref node y, ref node z) 
requires x::ll<n, S1> 
ensures y'::ll<m, S2> * z'::ll<p, S3> /*& n=m+p*/ & S1 = union(S2, S3) & forall( b : (b notin S2 | b<=a) ) 
& forall( c : (c notin S3 | b>a) );
{
	if (x==null) {
		y = null;
		z = null;
		return;
	}
	else {
		part(a, x.next, y, z);
		if (x.val <= a)	y = new node(x.val, y);
		else z = new node(x.val, z);
		return;
	}
}

void part1(int a, node x, ref node y, ref node z) 
requires x::ll1<n> 
ensures y'::ll1<m> * z'::ll1<p> & n=m+p ;
{
	if (x==null) {
		y = null;
		z = null;
		return;
	}
	else {
		part1(a, x.next, y, z);
		if (x.val <= a)	y = new node(x.val, y);
		else z = new node(x.val, z);
		return;
	}
}

void part2(int a, node x, ref node y, ref node z) 
requires x::ll2<S1> 
ensures y'::ll2<S2> * z'::ll2<S3> & S1 = union(S2, S3) & forall( b : (b notin S2 | b<=a) ) 
& forall( c : (c notin S3 | b>a) );
{
	if (x==null) {
		y = null;
		z = null;
		return;
	}
	else {
		part2(a, x.next, y, z);
		if (x.val <= a)	y = new node(x.val, y);
		else z = new node(x.val, z);
		return;
	}
}




