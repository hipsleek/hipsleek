/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> // = q1 
	inv n >= 0;

void insert(node2 x, int a)
  requires x::dll<p, n> & n>0 & Term[n] //&  x!=null  
  ensures x::dll<p, m> & m>n; 
{
  bool l = x.next == null;
  if (l)
			x.next = new node2(a, x, null);
		else 
      insert(x.next, a);
}

/* delete a node from a doubly linked list */
void delete(node2 x, int a)
	requires x::dll<p, n> & n > a & a > 0 & Term[n] 
	ensures x::dll<p, n-1>;
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

void delete1(node2 x, int a)
	requires x::dll<p, n> & n > a > 0 & Term[n] 
	ensures x::dll<p, n-1>;

{
	if (a == 1) 
	{
    node2 l = x.next.next;
		if (l!= null)
		{
      l.prev = x;
     // assume false;
		}
		x.next = l;
	}
	else
  {
		delete1(x.next, a-1);
    //assume false;
  }
}


void test_del(node2 x)
	requires x::dll<p, n> & n>1 & Term
	ensures x::dll<_,_>;
{
	node2 tmp1 = x.next;

	node2 tmp2 = tmp1.next;

	if (tmp2 != null) {

		tmp2.prev = x;
	}

	x.next = tmp2;
}

void test_del2(node2 x, node2 tmp2)
	requires 	x::node2<_,_,_> * tmp2::dll<x, _> & tmp2!=null & Term
			or	x::node2<_,_,_> & tmp2=null & Term
	ensures		x::dll<_,_>;
{
	if (tmp2 != null) {
		tmp2.prev = x;
	}
	x.next = tmp2;
}

node2 test_fold()
	requires Term
	ensures res::dll<_, 3>;
{
	node2 tmp_null = null;
	node2 tmp1 = new node2(10, tmp_null, tmp_null);

	node2 tmp2 = new node2(20, tmp_null, tmp1);
	tmp1.prev = tmp2;
	node2 tmp3 = new node2(30, tmp_null, tmp2);
	tmp2.prev = tmp3;

	return tmp3;
}

/* append 2 doubly linked lists */
node2 append(node2 x, node2 y)

	requires x::dll<q, m> * y::dll<p, n> & Term[m]
	ensures res::dll<_, m+n>;

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

node2 append1(node2 x, node2 y)

	requires x::dll<q, m> * y::dll<p, n> & Term[m]
	ensures res::dll<_, m+n>;	

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
void append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n> & m>0 & Term[m]
	ensures x::dll<q, m+n>;

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

void f1(node2 x)
	requires x::dll<q, m> & m>0 & Term
	ensures x::dll<q, m>;
{
	int t = 0;
	t = t+1;
}

void f2(node2 x)
	requires x::dll<q, m> & m>0 & Term
	ensures  x::dll<q, m> & m>0;
{
	f1(x);
}
