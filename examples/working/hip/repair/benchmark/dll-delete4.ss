data node2 {
	node2 prev;
	node2 next;	
}

dll<p,n> == self = null & n = 0 
  or self::node2<p , q> * q::dll<self, n-1> & n > 0;

void delete(node2 x, int a)
	requires x::dll<p, n> & n > a & a > 0 
	ensures x::dll<p, n-1>;
{
	if (a == 1){
		if (x.next.next != null)	{
			x.next.prev = x;
      // x.next.next.prev = x;
      node2 tmp = x.next;
      x.next = x.next.next;
      free tmp;
		}
		else      
			x.next = null;
	}
	else {
		delete(x.next, a-1);
	}
}

// if (v_bool_22_1946) [LABEL! 109,0: {((({fcode$node2~int(x,a)};
// (node2 tmp;
// tmp = bind x to (prev_24_1933,next_24_1934) [read] in 
// next_24_1934));
// {(node2 v_node2_25_1940;
// (v_node2_25_1940 = {(node2 v_node2_25_1937;
// (v_node2_25_1937 = bind x to (prev_25_1935,next_25_1936) [read] in 
// next_25_1936;
// bind v_node2_25_1937 to (prev_25_1938,next_25_1939) [read] in 
// next_25_1939))};
// bind x to (prev_25_1941,next_25_1942) [write] in 
// next_25_1942 = v_node2_25_1940))});
// free tmp)}]
