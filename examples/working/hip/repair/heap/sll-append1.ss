data node {
   node next;
}

ll<n> == self = null & n = 0
      or self::node<q> * q::ll<n-1>
      inv n >= 0;

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

// !!! **songbird.ml#844:vdefns:[  # pred PP(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ emp & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred T0(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ x'->node{nil} * ll(y',n2) & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred T2(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ x'->node{nil} * ll(y',n2) & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred QQ(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ emp & nil=y' & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]],

// # pred PP(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ ll(y',n2) & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred T0(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ x'->node{nil} & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred T2(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ x'->node{nil} & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred QQ(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ emp & -n2<=0 & y=y' & x=x' & q_7335=nil & n2=0 & flted_6_7334=0 & n1-1=0 ]],

// # pred PP(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ x'->node{nil} & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred T0(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ ll(y',n2) & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred T2(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ ll(y',n2) & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred QQ(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ x'->node{y'} & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]],

// # pred PP(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ x'->node{nil} * ll(y',n2) & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred T0(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ emp & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred T2(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ emp & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0 ]]
//   # pred QQ(n2,y',y,x',x,flted_6_7334,n1,q_7335) := [[ (exists q_10. x'->node{q_10} * ll(q_10,n2) & y=y' & x=x' & q_7335=nil & flted_6_7334=0 & n1-1=0) ]]]
