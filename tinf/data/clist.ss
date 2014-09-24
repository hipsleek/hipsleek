data node {
  int val;
  node next;
}

lseg<n, p> ==
  self = p & n = 0 or
  self::node<v, q> * q::lseg<n-1, p> 
  inv n>=0;

clist<n> ==
  self::node<v, q> * q::lseg<n-1, self>
  inv n>0;

lemma self::clist<n> <- self::lseg<n-1, q> * q::node<v, self>;

lemma self::lseg<n, q> <- self::lseg<n-1, p> * p::node<v, q>;

lemma self::node<v, q> * q::lseg<n, self> -> q::node<v1, s> * s::lseg<n, q>;

int length (node x)

  infer [@term]
  requires x::clist<n>@L
  ensures true;

/*  infer [@term]
  requires x::lseg<n,null>@L
  ensures res=n;

  infer [@term]
  requires x::lseg<n,null>
  ensures x::lseg<n,null> & res=n;
*/
{
  if (x == null)
    return 0;
  else
    return 1 + length(x.next);
}
/*
# clist.ss

  infer [@term]
  requires x::clist<n>@L
  ensures true;

Base/Rec Case Splitting:
[	length: [[2] 1<=n@R]
]
Termination Inference Result:
length:  requires x::clist<n> & truecase {
                             1<=n -> requires emp & Loop[]
 ensures false & false;
                             
Temporal Assumptions:
 termAssume flted_12_1342+1=n_1348 & v_1361=v_1343 & q_1360=self_1341 & 
!(v_bool_36_1214') & x'!=null & x'=x & self_1341=x' & flted_12_1342+1=n & 
v_int_39_1213'=v_int_39_1567+1 & res=v_int_39_1213' & (((q_1344=1 & x'=2 & 
1<=flted_12_1342) | (x'=1 & q_1344=self_1341 & 
flted_12_1342=0))) & lengthpost_1206(n_1348) --> lengthpost_1206(n).

 termAssume flted_12_1342+1=n & self_1341=x' & x'=x & x'!=null & 
!(v_bool_36_1214') & v_int_39_1212'=1 & v_node_39_1210'=q_1344 & 
q_1360=self_1341 & v_1361=v_1343 & flted_12_1342+1=n_1348 & (((q_1344=1 & 
x'=2 & 1<=flted_12_1342) | (x'=1 & q_1344=self_1341 & 
flted_12_1342=0))) & lengthpre_0(n) --> lengthpre_0(n_1348).

                             }

*/
