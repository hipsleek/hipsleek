data node {
  node next;
}

ll<n> == self=null & n = 0
  or self::node<r> * r::ll<n2> & n = 1 + n2;

int length(node x)
  requires x::ll<n>
  ensures x::ll<n> & res = n;
{
  if (x != null)
      return 5;
  else
      return 1 + length(x.next);
}


// {(boolean v_bool_12_1889;
// (v_bool_12_1889 = {is_not_null___$node(x)};
// if (v_bool_12_1889) [LABEL! 101,0: (int v_int_13_1881;
// (v_int_13_1881 = 5;
// ret# v_int_13_1881))]
// else [LABEL! 101,1: (int v_int_15_1888;
// (v_int_15_1888 = {((int v_int_15_1887;
// (v_int_15_1887 = 1;
// (int v_int_15_1886;
// v_int_15_1886 = {((node v_node_15_1884;
// v_node_15_1884 = bind x to (next_15_1882) [read] in 
// next_15_1882);
// length$node(v_node_15_1884) rec)})));
// add___$int~int(v_int_15_1887,v_int_15_1886))};
// ret# v_int_15_1888))]
// ))}
