/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<> == self = null
	or self::node<_, q> * q::ll<> 
  inv true;

	
lseg<p> == self = p
	or self::node<_, q> * q::lseg<p> 
  inv true;

void append(node x, node y)
 requires x::ll<> & x!=null
  ensures x::node<_,q>*q::lseg<y>;
  requires x::node<_,q>*q::ll<> 
  ensures  x::node<_,q2>*q2::lseg<y>;
{    
	if (x.next == null) 
           x.next = y;
	else
           append(x.next, y);
}


/*
# ex21f.ss

 requires x::ll<> & x!=null
  ensures x::node<_,q>*q::lseg<y>;
  requires x::node<_,q>*q::ll<> 
  ensures  x::node<_,q2>*q2::lseg<y>;

# What is this warning for?

WARNING: _0:0_0:0:* between overlapping heaps: ( v_node_31_1657'::node<Anon_1782,q>@M, q::lseg<y_1781>@M)

WARNING: _0:0_0:0:* between overlapping heaps: ( v_node_31_1657'::node<Anon_1782,q>@M, q::lseg<y_1781>@M)

WARNING: _0:0_0:0:* between overlapping heaps: ( v_node_31_1657'::node<Anon_1782,q>@M, q::lseg<y_1781>@M)

WARNING: _0:0_0:0:* between overlapping heaps: ( q::node<Anon_1782,q>@M, q::lseg<y'>@M)

WARNING: _0:0_0:0:* between overlapping heaps: ( q::node<Anon_1782,q>@M, q::lseg<y'>@M)

 */
