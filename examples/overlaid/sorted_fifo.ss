data node {
	int val;
	node next_f;
	node next_s;
}

ll<n>
	== self = null & n = 0
	or self::node<_,p,_> * p::ll<n-1>
	inv n >= 0;

sll<n,lb,ub>
	== self::node<lb,_,null> & lb = ub & n = 1
	or self::node<lb,_,q> * q::sll<n-1,lb1,ub> & q != null & lb <= lb1
	inv n >= 1 & lb <= ub;

node insert (node x, int v)
//requires x::ll<n> & x::sll<n,lb,ub> & n > 0
//ensures res::ll<n+1> & res::sll<n+1,lb1,ub1> & lb1 = min(v, lb) & ub1 = max(v, ub);

//requires x::ll<n> & n > 0
//ensures res::sll<n+1,lb1,ub1> & lb1 = min(v, lb) & ub1 = max(v, ub);
{
	node v_node = new node(v, null, null);
		 
	node fifo = insert_fifo(x,v_node);

	node fifo_sorted_list = insert_sorted_list(transform(fifo),v_node);

	return fifo_sorted_list;
}

node insert_fifo (node x, node v)
requires x::ll<n> * v::node<_,null,_> & n > 0
ensures	res::ll<n+1>;
{
	if (x.next_f == null) {
	   //assume false;
	   x.next_f = v;
	   return x;
	}
	else {
		//assume false;
		node xn = insert_fifo(x.next_f, v);
		x.next_f = xn;
		return x;
	}	
}

/*
Updating the sorted list chain after adding node v into the fifo.
Actually, x and v now are not separate.
*/

node insert_sorted_list (node x, node v)
//requires x::sll<n,lb,ub> & v::node<vv,_,null> & n > 0
requires x::sll<n,lb,ub> * v::node<vv,_,null> & n > 0
ensures res::sll<n+1,lb1,ub1> & lb1 = min(vv, lb) & ub1 = max(vv, ub);
{
	if (v.val <= x.val) {
		//assume false;
		v.next_s = x;
		return v;
	} else if (x.next_s != null) {
	    //assume false;
		node xn = insert_sorted_list(x.next_s, v);
		x.next_s = xn;
		return x;
	} else {
		//assume false;
		x.next_s = v;
		return x;
	}
}

node transform (node x)
requires x::ll<n> & n > 0
ensures res::sll<n,_,_>;
