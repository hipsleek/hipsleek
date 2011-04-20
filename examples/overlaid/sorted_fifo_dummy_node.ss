data node {
	int val;
	node next_f;
	node next_s;
}

ll<n>
	== self = null & n = 0
	or self::node<_,p,_@I> * p::ll<n-1>
	inv n >= 0;

sll<n,lb,ub>
	== self::node<lb,_@I,null> & lb = ub & n = 1
	or self::node<lb,_@I,q> * q::sll<n-1,lb1,ub> & q != null & lb <= lb1
	inv n >= 1 & lb <= ub;

void insert (node x, int v)

requires x::node<_,p,q>@I * (p::ll<n> & q::sll<n,lb,ub>) //x is a dummy node
ensures (p::ll<n+1> & q'::sll<n+1,lb1,ub1>) & lb1 = min(v, lb) & ub1 = max(v, ub);

{
	node v_node = new node(v, null, null);
		 
	insert_fifo(x,v_node);

	insert_sorted_list(x,v_node);
}

void insert_fifo (node x, node v)

requires x::node<_,p,q>@I * (p::ll<n> & q::sll<n,_,_>@I) * v::node<_,null,_> 
ensures p::ll<n+1> & (q::sll<n,_,_> * v::node<_,null,_>); //the fifo now includes v, while the sorted list does not

{
	if (p.next_f == null) {
	   p.next_f = v;
	}
	else {
		node xn = insert_fifo(p.next_f, v);
		p.next_f = xn;
	}	
}

/*
Updating the sorted list chain after adding node v into the fifo.
Actually, x and v now are not separate.
*/

node insert_sorted_list (node x, node v)

requires x::node<_,p,q>@I * (p::ll<_>@I & q::sll<n,_,_>) * v::node<_,null,_>
ensures res::sll<n+1,lb1,ub1> & lb1 = min(vv, lb) & ub1 = max(vv, ub);

{
	if (v.val <= q.val) {
		v.next_s = q;
		return v;
	} else if (q.next_s != null) {
		node xn = insert_sorted_list(q.next_s, v);
		q.next_s = xn;
		return q;
	} else {
		q.next_s = v;
		return q;
	}
}
