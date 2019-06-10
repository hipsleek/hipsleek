data node {
  node next;
}

ll<n> == self=null & n = 0
  or self::node<r> * r::ll<n2> & n = 1 + n2;

int length(node x)
  requires x::ll<n>
  ensures x::ll<n> & res = n;
{
  if (x == null) return 0;
  else return 3 + length(x.next);
}


// {(boolean v_bool_12_1889;
// (v_bool_12_1889 = {is_null___$node(x)};
// if (v_bool_12_1889) [LABEL! 101,0: (int v_int_12_1881;
// (v_int_12_1881 = 0;
// ret# v_int_12_1881))]
// else [LABEL! 101,1: (int v_int_13_1888;
// (v_int_13_1888 = {((int v_int_13_1887;
// (v_int_13_1887 = 3;
// (int v_int_13_1886;
// v_int_13_1886 = {((node v_node_13_1884;
// v_node_13_1884 = bind x to (next_13_1882) [read] in 
// next_13_1882);
// length$node(v_node_13_1884) rec)})));
// add___$int~int(v_int_13_1887,v_int_13_1886))};
// ret# v_int_13_1888))]
// ))}

// int length(node x)
//   requires x::ll<n>
//   ensures x::ll<n> & res = n;
// {
//   bool b = x == null;
//   if (b) {
//      int k1;
//      k1 = 0;
//      return k1;
//   }
//   else {
//     int k2;
//     // k2 = 3;
//     node n1;
//     // n1 = x.next;
//     int k3;
//     k3 = length(n1);
//     int k4;
//     k4 = k2 + k3;
//     return k4;
//   }
// }
