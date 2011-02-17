/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
	or self::node2<_ ,p , q> * q::dll<q1, n-1> & self = q1 
	inv n >= 0;

dll1<p, S> == self = null & S = {}
  or self::node2<v, p, q> * q::dll1<q1, S1> & self = q1 & S = union(S1, {v});

dll2<p, n, S> == self = null & S = {} & n = 0
  or self::node2<v, p, q> * q::dll2<q1, n-1, S1> & self = q1 & S = union(S1, {v});


void insert(node2 x, int a)
	//********************** MULTI PRE/POST *******************************************
	/*requires x::dll<p, n> & n > 0 
     	ensures x::dll<p, n+1>; 
	
	requires x::dll1<p, S> & S != {}
	ensures x::dll1<p, S1> & S1 = union(S, {a});
  	*/
	//********************** SINGLE PRE/POST *******************************************
  	requires x::dll2<p, n, S> & S != {}
	ensures x::dll2<p, n+1, S1> & S1 = union(S, {a});
{
	node2 tmp_null = null;

	if (x.next == null) {
		x.next = new node2(a, x, tmp_null);
	}
	else {
		insert(x.next, a);
	}
}


/* delete a node from a doubly linked list */
void delete(node2 x, int a)
	requires x::dll<p, n> & n > a & a > 0 
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

void test_del(node2 x)
	requires x::dll<p, n> & n>1
	ensures x::dll<_,_>;
{
	node2 tmp1 = x.next;

	node2 tmp2 = tmp1.next;

	if (tmp2 != null) {

		tmp2.prev = x;
	}

	//dprint;

	//assert x'::node2<_,_,_> * tmp2'::dll<x', _> & tmp2'!=null or x'::node2<_,_,_> & tmp2'=null;

	x.next = tmp2;

	//assert /*true assume*/ x'::node2<_,_,tmp2'> * tmp2'::dll<x', _> & tmp2'!=null or x'::node2<_,_,tmp2'> & tmp2'=null;

	//assert x'::dll<_,_>;
}

void test_del2(node2 x, node2 tmp2)
	requires 	x::node2<_,_,_> * tmp2::dll<x, _> & tmp2!=null
			or	x::node2<_,_,_> & tmp2=null
	ensures		x::dll<_,_>;
{
	if (tmp2 != null) {
		tmp2.prev = x;
	}
	x.next = tmp2;
}

node2 test_fold()
	requires true
	ensures res::dll<_, 3>;
{
	node2 tmp_null = null;
	node2 tmp1 = new node2(10, tmp_null, tmp_null);

	//debug on;
	//assert tmp1'::dll<_,1>;
	//debug off;

	node2 tmp2 = new node2(20, tmp_null, tmp1);
	tmp1.prev = tmp2;
	node2 tmp3 = new node2(30, tmp_null, tmp2);
	tmp2.prev = tmp3;

	//dprint;

	return tmp3;
}

/* append 2 doubly linked lists */
node2 append(node2 x, node2 y)
	//********************** MULTI PRE/POST *******************************************	
	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, m+n>;
	
	requires x::dll1<q, S1> * y::dll1<p, S2>
	ensures res::dll1<_, S> & S = union(S1, S2);
	//********************** SINGLE PRE/POST *******************************************	
	//requires x::dll2<q, n1, S1> * y::dll2<p, n2, S2>
	//ensures res::dll2<_, n1+n2, S> & S = union(S1, S2);
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

/* append 2 doubly linked lists */
void append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n> & m>0
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
	requires x::dll<q, m> & m>0
	ensures x::dll<q, m>;
{
	int t = 0;
	t = t+1;
}

void f2(node2 x)
	requires x::dll<q, m> & m>0
	ensures  x::dll<q, m> & m>0;
{
	f1(x);
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
