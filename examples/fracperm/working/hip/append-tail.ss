data node {
	int val;
	node next;
}


/* ll_tail<tx> == self::node<_, null> & tx=self */
/* 	or self::node<_, r> * r::ll_tail<tx> & r!=null; */

/* lseg<p> == self=p */
/* 	or self::node<_, r> * r::lseg<p>; */

lseg2<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg2<p, n-1>
	inv n>=0;

ll_tail2<tx, n> == self::node<_, null> & tx=self & n=1
	or self::node<_, r> * r::ll_tail2<tx, n-1> & r!=null
	inv self!=null & tx!=null & n>=1;

	

lemma "lseg2" self::lseg2<p, n> <- self::lseg2<q, n1> * q::lseg2<p, n2> & n=n1+n2;
lemma "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<t, n-1> * t::node<_, null>;
//coercion "ll_tail2_1" self::ll_tail2<t, n> <-> self::lseg2<q, a> * q::lseg2<t, b> * t::node<_, null> & n=a+b+1;


/* coercion "split_ll_tail" self::ll_tail2(f)<t,b> & f=f1+f2 & 0.0<f1<=1.0 & 0.0<f2<=1.0 -> self::ll_tail2(f1)<t,b> * self::ll_tail2(f2)<t,b> & 0.0<f<=1.0; */

/* coercion "split_lseg2" self::lseg2(f)<p,n> & f=f1+f2 & 0.0<f1<=1.0 & 0.0<f2<=1.0 -> self::lseg2(f1)<p,n> * self::lseg2(f2)<p,n> & 0.0<f<=1.0; */

/* coercion "split_node" self::node(f)<v,n> & f=f1+f2 & 0.0<f1<=1.0 & 0.0<f2<=1.0 -> self::node(f1)<v,n> * self::node(f2)<v,n> & 0.0<f<=1.0; */

//coercion "composite" self::lseg2<y, n> * y::lseg2<ty, m-1> * ty::node<_, null> <-> self::ll_tail2<ty, m+n>;
//coercion self::lseg2<p, n> -> self::lseg2<q, n-1> * q::node<_, p>;
//coercion "lsegbreakmerge" self::lseg<p> <-> self::lseg<q> * q::lseg<p>;
//coercion "lltail2lseg" self::ll_tail<t> <-> self::lseg<t> * t::node<_, null>;
//coercion "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<q, a> * q::lseg2<t, b> * t::node<_, null> & n=a+b+1;

// fail because of insufficient permission
//we write to x
//we only read y but we tie up x and y
void append(node x, node tx, node y, node ty)

  requires x::ll_tail2(0.5)<tx, n> * y::ll_tail2(0.5)<ty, m>
  ensures x::ll_tail2(0.5)<ty, m+n>;

{
	tx.next = y;
}

//valid
//we write to x
//we only read y but we tie up x and y
void append2(node x, node tx, node y, node ty)

  requires x::ll_tail2(1.0)<tx, n> * y::ll_tail2(1.0)<ty, m>
  ensures x::ll_tail2(1.0)<ty, m+n>;

{
	tx.next = y;
}


/*
****************************************************************************************************************************
 coercion "ll_tail2" self::ll_tail2<t, n>
   <-> self::lseg2<q, a> * q::lseg2<t, b> * t::node<_, null> & n=a+b+1;

This is a composite of lseg and ll_tail2 lemma. A hand-trace
looks like below. Please check if it works!

===============
x::ll_tail2<tx, n> * y::ll_tail2<ty, m> |- tx:node(_,_)

x::lseg2<tx, n-1> * tx:node<_,null> * y::ll_tail2<ty, m>

  {tx.nexy = y }

x::lseg2<tx, n-1> * tx:node<_,y> * y::ll_tail2<ty, m>
    |- x::ll_tail2<ty, m+n>

x::lseg2<tx, n-1> * tx:node<_,y> * y::ll_tail2<ty, m>
    |- x::lseg2<q,a> * q::lseg2<ty,b> * ty::node<_,null>
              & a+b+1=m+n

tx:node<_,y> * y::ll_tail2<ty, m>
    |- tx::lseg2<ty,b> * ty::node<_,null>
              & n-1+b+1=m+n

tx:node<_,y> * y::ll_tail2<ty, m>
    |- tx::node(_,q)*q::lseg2<ty,b-1> * ty::node<_,null>
              & n-1+b+1=m+n

y::ll_tail2<ty, m>
    |- y::lseg<ty,b-1> * ty::node<_,null>
              & n-1+b+1=m+n

y::lseg2<ty, m-1> * ty::node<_, null> 
	|- y::lseg<ty,b-1> * ty::node<_,null>
              & n-1+b+1=m+n	

ty::node<_, null>		
	|- ty::node<_,null>
              & n-1+b+1=b+n	
		  
*/
