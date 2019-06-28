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
		// x.next = y;
    x.next = y.next;
    y.prev = x;
	}
	else {
		append2(x.next, y);
	}
}

// self_7493->node2{p_7492,f_r_7542} * dll(y,b,n) & 0-n<0 & x=self_7493 & a=p_7492
// & q_7495=nil & flted_7_7494=0 & m-1=0 & f_r_7542=nil |-
// PP(y,b,n,x,self_7493,a,p_7492,q_7495,flted_7_7494,m,f_r_7542) & 0-n<0 &
// x=self_7493 & a=p_7492 & q_7495=nil & flted_7_7494=0 & m-1=0 & f_r_7542=nil,

// QQ(y,b,n,x,self_7493,a,p_7492,q_7495,flted_7_7494,m,f_r_7542) & 0-n<0 &
// q_7495=nil & flted_7_7494=0 & m-1=0 & f_r_7542=nil & a=p_7492 & x=self_7493 |-
// (exists prev_16_1923',next_16_1924'. y'->node2{prev_16_1923',next_16_1924'} *
// T4(y,b,n,q_7495,flted_7_7494,m,f_r_7542,a,p_7492,x,self_7493,prev_16_1923',next_16_1924')
// & 0-n<0 & q_7495=nil & flted_7_7494=0 & m-1=0 & f_r_7542=nil & a=p_7492 &
// x=self_7493),

// y'->node2{x',next_16_1924'} *
// T4(y,b,n,q_7495,flted_7_7494,m,f_r_7542,a,p_7492,x,self_7493,prev_16_11058,next_16_1924')
// & 0-n<0 & q_7495=nil & flted_7_7494=0 & m-1=0 & f_r_7542=nil & a=p_7492 &
// x=self_7493 |- (exists f_r_7543,q_4,q_18. q_4->node2{self_7493,q_18} *
// self_7493->node2{p_7492,q_4} * dll(q_18,q_4,f_r_7543) & 0-n<0 & q_7495=nil &
// flted_7_7494=0 & m-1=0 & f_r_7542=nil & a=p_7492 & x=self_7493 & x=self_7493 &
// a=p_7492 & q_7495=nil & (m-1)-flted_7_7494=0 & f_r_7543=flted_7_7494+(n-1)); 


// x->node2{p_7492,f_r_7542} * dll(y',b,n) & 0-n<0 & y=y' & self_7493=x & x'=x &
// a=p_7492 & q_7495=nil & flted_7_7494=0 & m-1=0 & f_r_7542=nil |-
// PP(b,n,y,y',self_7493,x',x,a,p_7492,q_7495,flted_7_7494,m,f_r_7542) & 0-n<0 &
// y=y' & self_7493=x & x'=x & a=p_7492 & q_7495=nil & flted_7_7494=0 & m-1=0 &
// f_r_7542=nil,

// QQ(b,n,y,y',self_7493,x',x,a,p_7492,q_7495,flted_7_7494,m,f_r_7542) & 0-n<0 &
// q_7495=nil & flted_7_7494=0 & m-1=0 & f_r_7542=nil & a=p_7492 & x'=x &
// self_7493=x & y=y' |- (exists prev_16_1923',next_16_1924'.
// y'->node2{prev_16_1923',next_16_1924'} *
// T4(b,n,q_7495,flted_7_7494,m,f_r_7542,a,p_7492,x',self_7493,x,y,y',prev_16_1923',next_16_1924')
// & 0-n<0 & q_7495=nil & flted_7_7494=0 & m-1=0 & f_r_7542=nil & a=p_7492 & x'=x &
// self_7493=x & y=y'),

// y'->node2{x',next_16_1924'} *
// T4(b,n,q_7495,flted_7_7494,m,f_r_7542,a,p_7492,x',self_7493,x,y,y',prev_16_11058,next_16_1924')
// & 0-n<0 & q_7495=nil & flted_7_7494=0 & m-1=0 & f_r_7542=nil & a=p_7492 & x'=x &
// self_7493=x & y=y' |- (exists f_r_7543,q_4,q_60. q_4->node2{x,q_60} *
// x->node2{p_7492,q_4} * dll(q_60,q_4,f_r_7543) & 0-n<0 & q_7495=nil &
// flted_7_7494=0 & m-1=0 & f_r_7542=nil & a=p_7492 & x'=x & self_7493=x & y=y' &
// y=y' & self_7493=x & x'=x & a=p_7492 & q_7495=nil & (m-1)-flted_7_7494=0 &
// f_r_7543=flted_7_7494+(n-1));

