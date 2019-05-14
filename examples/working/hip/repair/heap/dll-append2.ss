data node2 {
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or (exists q: self::node2<p , q> * q::dll<self, n-1> & n > 0);

void append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n> & m>0
	ensures x::dll<q, m+n>;
{
	if (x.next == null) {
    x.next = y.next;
    // P(x,y) -> Q(x,y)
    // x.next = y;
    // dprint;
    if (y != null) y.prev = x;
	}
	else {
		append2(x.next, y);
	}
}

// Q(x,y) := x::node<p, y> * y ::dll<q, n> & m = 1 & nxt = null

// Q(x',y') & v_bool_18_4433' & p_4457=q & self_4458=x' & x'=x & y'=y & q_4460=nil
// & flted_8_4459+1=m & 0<m & v_bool_14_4439' & y'!=nil

// |- (exists
// prev_18_4431',next_18_4432'. y'->node2{prev_18_4431',next_18_4432'} *
// T0(p_4457,q,self_4458,x',x,y,q_4460,flted_8_4459,m,y')) 

// y'->node2{x',next_18_4432'} *
// T0(p_4457,q,self_4458,x',x,y,q_4460,flted_8_4459,m,y') & v_bool_18_4433' &
// p_4457=q & self_4458=x' & x'=x & y'=y & q_4460=nil & flted_8_4459+1=m & 0<m &
// v_bool_14_4439' & y'!=nil |- (exists q_2062,flted_12_2061.
// dll(x,q_2062,flted_12_2061) & flted_12_2061=n+m & q_2062=q)

// Q(x',y') & !(v_bool_18_4433') & p_4457=q & self_4458=x' & x'=x & y'=y &
// q_4460=nil & flted_8_4459+1=m & 0<m & v_bool_14_4439' & y'=nil |- (exists
// q_2062,flted_12_2061. dll(x,q_2062,flted_12_2061) & flted_12_2061=n+m &
// q_2062=q) 

// Q(x,y) := [[ dll(x,q,flted_8_4459+n+1) & y=nil ]]

// expected: q_1954::dll<x,flted_8_1953> * y::dll<p,n> * x'::node2<q,y'>&
//  y'=y & x=x' & q_1954=null & flted_8_1953=m-1 & 1<=m 