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


relation INSERT(bag a, bag b, int c).
relation INSERTNUM(int d, int e).
void insert(node2 x, int a)
  infer [INSERT,INSERTNUM]
  requires x::dll<p, n, S> & x!=null
  ensures x::dll<p, m, S1> & INSERTNUM(m,n) & INSERT(S,S1,a); //& S1=S+{a}
{
  if (x.next == null)
    x.next = new node2(a, x, null);
  else 
    insert(x.next, a);
}

/*
/* delete a node from a doubly linked list */
relation DEL(int a, int b, int c).
void delete(node2 x, int a)
  infer [DEL,n,a]
	requires x::dll<p, n> //& n > a & a > 0 
	ensures x::dll<p, m> & DEL (n,a,m); // n=m+1
{
	node2 tmp;
	node2 tmp_null = null;

	if (a == 1) 
	{
		if (x.next.next != null)
		{
			x.next.next.prev = x;
			tmp = x.next.next;
			x.next = tmp;
		}
		else
			x.next = tmp_null;
	}
	else {
		delete(x.next, a-1);
	}
}

relation DEL1(int a, int b, int c).
void delete1(node2 x, int a)
  infer [DEL1,n,a]
	requires x::dll<p, n> //& n > a > 0 
	ensures x::dll<p, m> & DEL1(n,m,a); // n=m+1

{
	if (a == 1) 
	{
    node2 l = x.next.next;
		if (l!= null)
		{
      l.prev = x;
		}
		x.next = l;
	}
	else
  {
		delete1(x.next, a-1);
  }
}


/* append 2 doubly linked lists */
relation APP(int a, int b, int c).
node2 append(node2 x, node2 y)
  infer [APP]
	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, t> & APP(t,m,n); // t=m+n

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

relation APP1(int a, int b, int c).
node2 append1(node2 x, node2 y)
  infer [APP1]
	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, t> & APP1(t,m,n);	//t=m+n
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

/* append 2 doubly linked lists */
relation APP2(int a, int b, int c).
void append2(node2 x, node2 y)
  infer [m,APP2]
	requires x::dll<q, m> * y::dll<p, n> //m>=1
	ensures x::dll<q, t> & APP2(t,n,m); //t=m+n
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
*/

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
