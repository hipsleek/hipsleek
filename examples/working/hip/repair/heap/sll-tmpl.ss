data node {
  node next;	
}

lseg<p,n> == self = p & n = 0 
or self::node<u> * u::lseg<p,n-1> & n > 0;

HeapPred P1(node x, node y).
HeapPred Q1(node x, node y).

void fcode1(node x, node y)
   requires P1(x,y)
   ensures Q1(x,y);

node reverse(node x)
requires x::lseg<y, n> * y::node<null>
ensures y::lseg<x, n> * x::node<null> & res = y;
{
  if (x==null){
     return null;
   }
  else if (x.next == null){
     return x;
  }
  else {
     node k;
     fcode1(x, k);
     x.next.next = x;
     x.next = null;
     return k;
  }
}

// dynamic  EBase 
//    hfalse&false
// {(boolean v_bool_19_1939;
// (v_bool_19_1939 = {is_null___$node(x)};
// if (v_bool_19_1939) [LABEL! 104,0: {(null_type v_null_type_20_1927;
// (v_null_type_20_1927 = null;
// ret# v_null_type_20_1927))}]
// else [LABEL! 104,1: (boolean v_bool_22_1938;
// (v_bool_22_1938 = {((node v_node_22_1930;
// v_node_22_1930 = bind x to (next_22_1928) [read] in 
// next_22_1928);
// is_null___$node(v_node_22_1930))};
// if (v_bool_22_1938) [LABEL! 105,0: {ret# x}]
// else [LABEL! 105,1: {((((node k;
// {fcode1$node~node(x,k)});
// {(node v_node_28_1934;
// (v_node_28_1934 = bind x to (next_28_1933) [write] in 
// next_28_1933;
// bind v_node_28_1934 to (next_28_1935) [write] in 
// next_28_1935 = x))});
// {(null_type v_null_type_29_1936;
// (v_null_type_29_1936 = null;
// bind x to (next_29_1937) [write] in 
// next_29_1937 = v_null_type_29_1936))});
// ret# k)}]
// ))]
// ))}
