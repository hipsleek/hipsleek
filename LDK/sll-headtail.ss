/*
 * linked list with 2 dummy nodes head and tail: ll_ht
 */

data node {
	int val; 
	node next;	
}


/*
// sorted list with dummy tail
ll_tail<n, t, sm, lg> == self::node<sm, t> * t::node< _, null> & n=1 & sm=lg
		or self::node<sm, r> * r::ll_tail<n-1, t, sm1, lg> & r!=null & sm<=sm1
	inv n>=0 & self!=null;


// view of a sorted list with dummy head and tail
ll_ht<n, h, t, sm, lg> == self::node<_, p> * p::node<sm,t> * t::node<_,null> & self=h & n=1 & sm=lg
  or self::node<_, p> * p::node<sm, r> * r::ll_ht<n-1, p, t, sm1, lg> & self=h & r!=null & sm<=sm1
	inv n>=0 & self!=null;
/*
