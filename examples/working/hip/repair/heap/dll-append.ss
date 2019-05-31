data node2 {
	node2 prev;
	node2 next;	
}

dll<p,n> == self = null & n = 0 
  or (exists q: self::node2<p , q> * q::dll<self, n-1> & n > 0);

void append2(node2 x, node2 y)
	requires x::dll<a, m> * y::dll<b, n> & m>0 & n > 0
	ensures x::dll<a, m+n>;
{
	if (x.next == null) {
		x.next = y;
    // x.next = y.next;
    y.prev = x;
	}
	else {
		append2(x.next, y);
	}
}

// x::dll<q, m> * y::dll<p,n> & m > 0 & n > 0
// x::node<q,nxt> * y::dll<p, n> & m = 1 & nxt = null & n > 0
// Q() & m = 1 & nxt = null & n > 0 |- (exists ynxt, yprv. y::node2{yprv, ynxt} * T).
// y -> node2(x, ynxt) * T |- post

// QQ(b,n,y',y,x,self_4533,x',p_4532,a,flted_8_4534,m,q_4535)

// Q(x',y') & v_bool_14_4509' & 0<n & 0<m & flted_8_4534+1=m &
// q_4535=nil & p_4532=q & self_4533=x & x'=x & y'=y |- (exists
// prev_16_4502',next_16_4503'. y'->node2{prev_16_4502',next_16_4503'} *
// T0(n,flted_8_4534,m,q_4535,p_4532,q,self_4533,x',x,y',y))

// y'->node2{x',next_16_4503'} *
//   T0(n,flted_8_4534,m,q_4535,p_4532,q,self_4533,x',x,y',y) & v_bool_14_4509' &
//   0<n & 0<m & flted_8_4534+1=m & q_4535=nil & p_4532=q & self_4533=x & x'=x &
//   y'=y |- (exists q_2133,flted_12_2132. dll(x,q_2133,flted_12_2132) &
//   flted_12_2132=n+m & q_2133=q) 