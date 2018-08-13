func int tf(int k) == ?.

data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<sum> == self=null & sum = 0
	or self::node<v, r> * r::ll<sum2> & sum = v + sum2;

int sum(node x)
requires x::ll<n> ensures res = n;
{
  if (x == null) return 0;
  else {
       int k;
       k = sum(x.next);
       return x.val - tf(k);
//       dprint;
  }
}


// data node {
// 	int val;
// 	node next
// }

// /* view for a singly linked list */
// ll<sum> == self=null & sum = 0
// 	or self::node<v, r> * r::ll<sum2> & sum = v + sum2;

// int sum(node x)
// requires x::ll<n> ensures res = n;
// {
//   if (x == null) return 0;
//   else {
//        return 2 * x.val + sum(x.next);
//   }
// }


// # n_1914=sum2_1911 & k=n_1914 & v_int_19_1887+tf(k)=v_1909 & n=sum2_1911+v_1909
//   & res=v_int_19_1887 |- res=n

//# n_1914=sum2_1911 & v_int_19_1887+tf(k)=v_1909 & n=sum2_1911+v_1909 &
//res=v_int_19_1887 |- res=n

// fc_current_ents: [( n_1914=sum2_1911 & k'=n_1914 & v_int_19_1887'+(tf( k'))=v_1909 &
//  n=sum2_1911+v_1909 & res=v_int_19_1887', res=n)]
//       }

// {(boolean v_bool_15_1888;
// (v_bool_15_1888 = {is_null___$node(x)};
// if (v_bool_15_1888) [LABEL! 102,0: (int v_int_15_1875;
// (v_int_15_1875 = 0;
// ret# v_int_15_1875))]
// else [LABEL! 102,1: {(((int k;
// k = {((node v_node_18_1880;
// v_node_18_1880 = bind x to (val_18_1876,next_18_1877) [read] in 
// next_18_1877);
// sum$node(v_node_18_1880) rec)});
// (int v_int_19_1887;
// (v_int_19_1887 = {((int v_int_19_1886;
// (v_int_19_1886 = bind x to (val_19_1881,next_19_1882) [read] in 
// val_19_1881;
// (int v_int_19_1885;
// v_int_19_1885 = tf(k)));
// minus___$int~int(v_int_19_1886,v_int_19_1885))};
// ret# v_int_19_1887)));
// dprint)}]
// ))}


// (==solver.ml#7580==)
// build_and_failures#1@1
// build_and_failures#1 inp1 :([],[],[( n_1914=sum2_1911 & k'=n_1914 & v_int_19_1887'+(tf( k'))=v_1909 & 
//  n=sum2_1911+v_1909 & res=v_int_19_1887', res=n)])
// build_and_failures#1@1 EXIT: failctxfe_kind: MAY
//         fe_name: logical bug
//         fe_locs: {
//     fc_message:  n=k'+res+(tf( k')) |-  res=n. LOCS:[0;18;10;19;13] (may-bug)
//     fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}
//     fc_current_ents: [( n_1914=sum2_1911 & k'=n_1914 & v_int_19_1887'+(tf( k'))=v_1909 & 
//  n=sum2_1911+v_1909 & res// =v_int_19_1887', res=n)]
// [( n_1914=sum2_1911 & v_int_19_1887'+(tf( k'))=v_1909 & n=sum2_1911+v_1909 & 
//  res=v_int_19_1887', res=n)]
//   }
// [[empty]]false
