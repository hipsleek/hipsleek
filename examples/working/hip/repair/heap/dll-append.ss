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

// {(boolean v_bool_13_1930;
// (v_bool_13_1930 = {((node2 v_node2_13_1917;
// v_node2_13_1917 = bind x to (prev_13_1913,next_13_1914) [read] in 
// next_13_1914);
// is_null___$node2(v_node2_13_1917))};
// if (v_bool_13_1930) [LABEL! 102,0: {({(node2 v_node2_15_1920;
// (v_node2_15_1920 = bind y to (prev_15_1918,next_15_1919) [read] in 
// next_15_1919;
// bind x to (prev_15_1921,next_15_1922) [write] in 
// next_15_1922 = v_node2_15_1920))};
// bind y to (prev_16_1923,next_16_1924) [write] in 
// prev_16_1923 = x)}]
// else [LABEL! 102,1: {{((node2 v_node2_19_1929;
// v_node2_19_1929 = bind x to (prev_19_1925,next_19_1926) [read] in 
// next_19_1926);
// append2$node2~node2(v_node2_19_1929,y) rec)}}]
// ))}
