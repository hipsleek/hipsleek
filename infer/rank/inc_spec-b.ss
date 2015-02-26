data node {
	int val;
	node next;
}

ll1<> == self=null 
	or self::node<_, q> * q::ll1<>
	inv true;

ll2<n> == self=null & n=0
	or self::node<_, q> * q::ll2<n-1>
	inv n>=0;

ll3<n,S> == self=null & n=0 & S={}
	or self::node<v, q> * q::ll3<n-1,S1> & S=union(S1,{v})
	inv n>=0;

ll4<S> == self=null & S={}
	or self::node<v, q> * q::ll4<S1> & S=union(S1,{v})
	inv true;

sll1<S> == self=null & S = {}
	or self::node<v2, r> * r::sll1<S1>
	& S = union(S1, {v2}) &	forall(x: (x notin S1 | v2 <= x));

sll2<n,S> == self=null & n=0 & S={}
	or self::node<v2, r> * r::sll2<n-1,S1> 
	& S = union(S1, {v2}) &	forall(x: (x notin S1 | v2 <= x))
  inv n>=0;

/*
sll1<S> == self::node<v1, null> & S = {v1}
	or self::node<v2, r> * r::sll1<S1> & r != null 
	& S = union(S1, {v2}) &	forall(x: (x notin S1 | v2 <= x));

sll2<n,S> == self::node<v1, null> & S = {v1} & n=1
	or self::node<v2, r> * r::sll2<n-1,S1> & r != null 
	& S = union(S1, {v2}) &	forall(x: (x notin S1 | v2 <= x));
*/

relation A(int a, int b, int c).

/*
node append1(node x, node y)
  requires x::ll1<>*y::ll1<> 
  ensures res::ll1<>;
{
        node r;
	if (x==null) return y;
	if (x.next!=null) {
		r = new node(x.val,null); 
		r.next = append1(x.next, y);
		return r;
	}
	else {
       	      	r = new node(x.val,y); 
		return r;
	}
}

node append2(node x, node y)
  requires x::ll2<n>*y::ll2<m> 
  ensures res::ll2<n+m>;
{
        node r;
	if (x==null) return y;
	if (x.next!=null) {
		r = new node(x.val,null); 
		r.next = append2(x.next, y);
		return r;
	}
	else {
       	      	r = new node(x.val,y); 
		return r;
	}
}


node append3(node x, node y)
  infer [A] 
  requires x::ll2<n>*y::ll2<m> & Term[n]
  ensures res::ll2<t> & A(t,m,n);
{
        node r;
	if (x==null) return y;
	if (x.next!=null) {
		r = new node(x.val,null); 
		r.next = append3(x.next, y);
		return r;
	}
	else {
	      	r = new node(x.val,y); 
		return r;
	}
}
*/

node append3(node x, node y)
  requires x::ll4<S1>*y::ll4<S2> 
  ensures res::ll4<S3> & S3=union(S1,S2);
{
    node r;
	if (x==null) return y;
    else {
     r = x.next;
     r = append3(r,y);
     x.next = r;
     return x;
    }
}

node append4(node x, node y)
  requires x::ll3<n,S1>*y::ll3<m,S2> 
  ensures res::ll3<n+m,S3> & S3=union(S1,S2);
{
    node r;
	if (x==null) return y;
    else {
     r = x.next;
     r = append4(r,y);
     x.next = r;
     return x;
    }
}


node append5(node x, node y)
  requires x::sll1<S1>*y::sll1<S2> 
        & forall(a: (a notin S1 | forall(b: (b notin S2 | a <= b))))
  ensures res::sll1<S3> & S3=union(S1,S2);

{
    node r;
	if (x==null) return y;
    else {
     r = x.next;
     r = append5(r,y);
     x.next = r;
     return x;
    }
}


node append6(node x, node y)
  requires x::sll2<n,S1>*y::sll2<m,S2> 
        & forall(a: (a notin S1 | forall(b: (b notin S2 | a <= b))))
  ensures res::sll2<n+m,S3> & S3=union(S1,S2);

{
    node r;
	if (x==null) return y;
    else {
     r = x.next;
     r = append6(r,y);
     x.next = r;
     return x;
    }
}
