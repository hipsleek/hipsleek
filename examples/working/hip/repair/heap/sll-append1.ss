data node {
   node next;
}

ll<n> == self = null & n = 0
      or self::node<q> * q::ll<n-1>;

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
{
  if (x.next == null){
     x.next = y.next;
  } else append(x.next, y);
}



// {(boolean v_bool_13_1897;
// (v_bool_13_1897 = {((node v_node_13_1889;
// v_node_13_1889 = bind x to (next_13_1886) [read] in 
// next_13_1886);
// is_null___$node(v_node_13_1889))};
// if (v_bool_13_1897)
// [LABEL! 101,0: {{(node v_node_14_1891;
// (v_node_14_1891 = bind y to (next_14_1890) [read] in 
// next_14_1890;
// bind x to (next_14_1892) [write] in 
// next_14_1892 = v_node_14_1891))}}]
// else [LABEL! 101,1: {((node v_node_15_1896;
// v_node_15_1896 = bind x to (next_15_1893) [read] in 
// next_15_1893);
// append$node~node(v_node_15_1896,y) rec)}]
// ))}
