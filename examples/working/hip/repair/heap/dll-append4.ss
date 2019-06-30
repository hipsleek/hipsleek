data node2 {
	node2 prev;
	node2 next;	
}

dll<p,n> == self = null & n = 0 
  or (exists q: self::node2<p , q> * q::dll<self, n-1> & n > 0)
	inv n >= 0;

void append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n> & m>0
	ensures x::dll<q, m+n>;
{
	if (x.next == null) {
    x.next = y.next;
    // x.next = y;
    // fcode(x,y);
    if (y != null) y.prev = x;
	}
	else {
		append2(x.next, y);
	}
}

// x'->node2{p_11038,q_11041} * dll(q_11041,self_11039,flted_7_11040) * dll(y,p,n) & v_bool_14_1933' & y'=y & x'=x & self_11039=x' & p_11038=q & 0<m & flted_7_11040+1=m & q_11041=nil |- PP(p,n,y',y,x,self_11039,x',p_11038,q,flted_7_11040,m,q_11041) & v_bool_14_1933' & y'=y & x'=x & self_11039=x' & p_11038=q & 0<m & flted_7_11040+1=m & q_11041=nil
//   # QQ(p,n,y',y,x,self_11039,x',p_11038,q,flted_7_11040,m,q_11041) & v_bool_18_1927' & y'=y & x'=x & self_11039=x & p_11038=q & q_11041=nil & flted_7_11040+1=m & 0<m & v_bool_14_1933' |- y->node2{prev_18_1925,next_18_1926} * T2(p,n,y',y,x',self_11039,x,p_11038,q,q_11041,flted_7_11040,m,prev_18_1925',next_18_1926') & v_bool_18_1927' & y'=y & x'=x & self_11039=x & p_11038=q & q_11041=nil & flted_7_11040+1=m & 0<m & v_bool_14_1933'
//   # y'->node2{x',next_18_1926'} * T2(p,n,y',y,x',self_11039,x,p_11038,q,q_11041,flted_7_11040,m,prev_18_11057,next_18_1926') & v_bool_18_1927' & y'=y & x'=x & self_11039=x & p_11038=q & q_11041=nil & flted_7_11040+1=m & 0<m & v_bool_14_1933' |- (exists q_105,flted_12_104. dll(x,q_105,flted_12_104) & v_bool_18_1927' & y'=y & x'=x & self_11039=x & p_11038=q & q_11041=nil & flted_7_11040+1=m & 0<m & v_bool_14_1933' & flted_12_104=n+m & q_105=q)
//   # QQ(p,n,y',y,x,self_11039,x',p_11038,q,flted_7_11040,m,q_11041) & !(v_bool_18_1927') & y'=y & x'=x & self_11039=x & p_11038=q & q_11041=nil & flted_7_11040+1=m & 0<m & v_bool_14_1933' |- (exists q_105,flted_12_104. dll(x,q_105,flted_12_104) & !(v_bool_18_1927') & y'=y & x'=x & self_11039=x & p_11038=q & q_11041=nil & flted_7_11040+1=m & 0<m & v_bool_14_1933' & flted_12_104=n+m & q_105=q)