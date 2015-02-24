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
{
	int cell_nos;
	try{
		list_alloc1(n,0,x,cell_nos);
	} catch (__Exc exc)	{
			list_dealloc(cell_nos, x);
			assert x'=null;
			raise (new no_mem_exc());
		}; 
}


// relaxed strong guarantee
void list_alloc1(int n, int i, ref node x, ref int cell_no) throws __Exc
requires x::ll<i> & n>=i & i>=0 
ensures x'::ll<n> & cell_no'=n & flow __norm or x'::ll<cell_no'> * res::__Exc<> & flow __Exc;
{
	if (n > i) {
		try {
			x = new2(0, x);
		}
		catch (__Exc exc)	{
			cell_no = i;
			raise (new __Exc());
			
		};
		list_alloc1(n, i+1, x, cell_no);
	}
	cell_no = n;
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