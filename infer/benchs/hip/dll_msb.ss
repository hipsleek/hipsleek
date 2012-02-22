/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size and bag */
dll<p,n,S> == self = null & n = 0 & S={}
  or self::node2<v ,p , q> * q::dll<self, n-1, S1> & S=union(S1, {v})
	inv n >= 0;

/* view for a doubly linked list with bag */
dll2<p,S> == self = null & S={}
  or self::node2<v ,p , q> * q::dll2<self, S1> & S=union(S1, {v})
	inv true;

relation INSERT(bag a, bag b, int c).
void insert(node2 x, int a)
  infer [INSERT]
  requires x::dll<p, n, S> & x!=null
  ensures x::dll<p, m, S1> & m=n+1 & INSERT(S,S1,a); //& S1=S+{a}
{
  if (x.next == null)
    x.next = new node2(a, x, null);
  else 
    insert(x.next, a);
}

// DLL without size property
relation APP(bag a, bag b, bag c).
node2 append0(node2 x, node2 y)
  infer [APP]
	requires x::dll2<q, S1> * y::dll2<p, S2>
	ensures res::dll2<_, S> & APP(S,S1,S2); // S=union(S1,S2)

{
	node2 tmp;
	if (x == null)
		return y;
	else
	{ 	
		tmp = x.next;
		tmp = append0(tmp, y);
		if (tmp != null)
		{
			x.next = tmp; 
			tmp.prev = x;
		}
		else {
			x.next = null;
		}
		return x; 
	}
}

relation APP(bag a, bag b, bag c).
node2 append(node2 x, node2 y)
  infer [APP]
	requires x::dll<q, m, S1> * y::dll<p, n, S2>
	ensures res::dll<_, t, S> & t=m+n & APP(S,S1,S2); // S=union(S1,S2)

{
	node2 tmp;
	if (x == null)
		return y;
	else
	{ 	
		tmp = x.next;
		tmp = append(tmp, y);
		if (tmp != null)
		{
			x.next = tmp; 
			tmp.prev = x;
		}
		else {
			x.next = null;
		}
		return x; 
	}
}


relation APP1(bag a, bag b, bag c).
node2 append1(node2 x, node2 y)
  infer [APP1]
	requires x::dll<q, m, S1> * y::dll<p, n, S2>
	ensures res::dll<_, t, S> & t=m+n & APP1(S,S1,S2);	// S=union(S1,S2)
{
	if (x == null)
		return y;
	else
	{	
		node2 tmp = append1(x.next, y);
		if (tmp != null)
			tmp.prev = x;
		x.next = tmp;
		return x;
	}
}

relation APP2(bag a, bag b, bag c).
void append2(node2 x, node2 y)
  infer [m,APP2]
	requires x::dll<q, m, S1> * y::dll<p, n, S2> //m>=1
	ensures x::dll<q, t, S> & t=m+n & APP2(S,S1,S2); //S=Union(S1,S2)
{
	node2 tmp;
	if (x.next == null) {
		x.next = y;
		if (y != null) {
			y.prev = x;
		}		
	}
	else {
		append2(x.next, y);
	}
}

/*
dlseg<sf, lf, sb, lb, n> == self=sf & n=0
			or self::node2<_, sf, r> * r::dlseg<self, lf, self, 

dlseg<p, q, n> == self=q & n=0
			or	self::node2<_, p, r> * r::dlseg<self, q, n-1>
			inv n>=0;
*/

/*
node2 append3(node2 x, node2 y)

	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, m+n>;

{
	if (x == null)
		return y;
	else { 	
		node2 tmp = find_last(x);
		tmp.next = y;
		return x;
	}
}
*/

/*
node2 find_last(node2 x)
	requires x::dll<q, m> & m>0
	ensures res::node2<_,p,null> * x::dlseg<q, res, m-1>;
{
	if (x.next == null) return x;
	else return find_last(x.next);
}
*/

/*
void id1(node2 x, node2 y)
	requires x::dlseg<q, y, n> * y::node2<_,
*/
