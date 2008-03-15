data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

ls<p, n> == self=p & n=0 
	or self::node<_, q> * q::ls<p, n-1> & self!=p
	inv n>=0;

ls_bag<p, n, B> == self = p & n = 0 & B = {} 
	or self::node<v, q> * q::ls_bag<p, n1, B1> & self != p & n = n1+1 & n > 0 & B = union({self}, B1)
	inv n >= 0 & p notin B;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;

cl<n> == self::node<_,p> * p::ls_bag<self,n1, _> & n = n1+1
	inv n>=1;

void append(node x, node y)
	//requires x::ll<n> & n>0
	//ensures x::lseg<y, n>;
	//requires x::ll<n> & y=x & n>0
	//ensures x::clist<n>;
	/*requires x::ls<null,n> * y::node<a,b> & x!=y & n>0
	ensures x::ls<y, n> * y::node<a,b>;*/
	/*requires x::ls<null,n> & y=x & n>0
	ensures x::cl<n>;*/
	
	requires x::ls_bag<null,n, B> & n>0 & y notin B
	ensures x::ls_bag<y, n, B>;
	//requires x::ls_bag<null, n, B> & n>0 & x = y 
	//ensures x::cl<n>;
	requires x::node<_, q> * q::ls_bag<null, n1, B> & x = y & y notin B
	ensures x::cl<n2> & n2 = n1+1;
{
	//dprint;
	//assert x'::ls_bag<_, _, _>;
	//node tmp;
	//tmp = x.next;
	//assert tmp'::ls_bag<_, _, _>;
	if (x.next != null) {
		//assume false;
		//assert x'::ls_bag<_, _, _>;
		//dprint;
		append(x.next, y);
		return;
	}
	else {
		x.next = y;
		//assert x'::cl<_>;
		//dprint;
		return;
	}
}

void test(node x)
requires x::ll<n> & n > 0
ensures x::node<1, q> * q::ll<n-1>;
{
	x.val = 1;
}
