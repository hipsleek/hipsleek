/* quick sort */

data node {
	int val; 
	node next; 
}

bnd<n, sm, bg> == self = null & n = 0 or 
      self::node<d, p> * p::bnd<n-1, sm, bg> & sm <= d < bg 
      inv n >= 0;

sll<n, sm, lg> == 
     self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 
  or self::node<sm, q> * q::sll<n-1, qs, lg> &  sm <= qs 
      inv n >= 1 & sm <= lg & self!=null ;

/* function to append 2 bounded lists */
node append_bll(node x, node y)
    requires y::sll<m,s2,b2> & x=null 
    ensures res::sll<m,s2,b2>;
	/* requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2 */
	/* ensures res::sll<nn+m, s0, b2>; */

{
        node xn; 
        if (x==null) {
          dprint;
          /*
       120y::sll<m,s2,b2>@M & x'=x & y'=y & x=null & xn_49'=null & 
        115x'=null & 112v_bool_26_206' & 113x'=null & v_bool_26_206' &
        several duplications above!
          */ 
          //assume false;
          return x;
        }/* segmentation BUG when returning null 
           with cvc3, redlog and omega */
        /* guard error with mona */
        /* correct answer is return y */
        else {
         xn = append_bll(x.next,y);
         x.next = xn;
         return x;
        }
}


