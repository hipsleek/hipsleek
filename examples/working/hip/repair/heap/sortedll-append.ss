data node {
	int val; 
	node next; 
}

sll<n, sm, lg> == 
     self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 
  or self::node<sm, q> * q::sll<n-1, qs, lg> &  sm <= qs 
      inv n >= 1 & sm <= lg & self!=null ;

void append(node x, node y)
     	requires x::sll<nn, s0, b0> * y::sll<m, s2, b2> & b0 <= s2 & x != null
	    ensures x::sll<nn+m, s0, b2>;

{
  	if (x.next == null){
       x.next = y.next;
    } else {
       append(x.next, y);
    }

}

// x::node<s0, fl> * y::sll