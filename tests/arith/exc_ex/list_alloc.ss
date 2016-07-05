/* singly linked lists */

/* representation of a node */
data node {
	   int val; 
	       node next;
}

class no_mem_exc extends __Exc {}

/* view for a singly linked list */
ll<n> == self = null & n = 0 
or self::node<_, q> * q::ll<n1> & n = n1 + 1
inv n >= 0;

node new2(int val, node next) throws no_mem_exc
requires true
ensures res::node<val, next> & flow __norm or res::no_mem_exc<> & flow no_mem_exc;
//requires true
//ensures res=null & flow no_mem_exc;

void dealloc (ref node x)
requires x::node<>
ensures x' = null;

// strong guarantee
void list_alloc_main(int n, ref node x) throws no_mem_exc
requires x = null & n>=0
ensures x'::ll<n> & flow __norm or res::no_mem_exc<> & x' = null & flow no_mem_exc;
{list_alloc(n,0,x);}

void list_alloc(int n, int i, ref node x) throws no_mem_exc
requires x::ll<i> & n>=i & i>=0
ensures x'::ll<n> & flow __norm or res::no_mem_exc<> & x' = null & flow no_mem_exc;
{
	if (n > i) {
		try {
			x = new2(0, x);
		}
		catch (no_mem_exc exc)	{
			list_dealloc(i, x);
			assert x'=null;
			raise (new no_mem_exc());
			//dprint;
			//return;
		};
		//dprint;
		assert x'::ll<_>;
		list_alloc(n, i+1, x);
	}
}

void list_dealloc(int n, ref node x)
requires x::ll<n> & n>=0
ensures x' = null;
{
	node y;
	if (n > 0) {
		y = x;
		x = x.next;
		dealloc(y);
		list_dealloc(n-1, x);
	}
}