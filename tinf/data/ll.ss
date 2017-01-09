data node { int val; node next }

ll<n> == 
	self = null & n = 0 or 
	self::node<v, p> * p::ll<n1> & n = n1 + 1
	inv n >= 0;

int length (node x)
	infer[@term]
	requires x::ll<n> 
	ensures true;
{
	if (x == null) return 0;
	else return 1 + length(x.next);
}
/*
# ll.ss

int length (node x)
	infer[@term]
	requires x::ll<n> 
	ensures true;

I guess we need to express in terms of integer vars..

Why did we get x=1 and x=0 for node type?

Base/Rec Case Splitting:
[	length: [[2] x=1@R,[3] x=0@B]
]
Termination Inference Result:
length:  requires x::ll<n> & truecase {
                          x=1 -> requires emp & Term[62,3]
 ensures emp & true;
                          
                          x=0 -> requires emp & Term[62,1]
 ensures emp & true;
                          
                          }

Temporal Assumptions:
 termAssume 0<=n1_1223 & n_1225=n1_1223 & !(v_bool_13_1184') & x'!=null & 
!(v_bool_13_1184') & x'=x & x'!=null & n=1+n1_1223 & 
v_int_14_1183'=v_int_14_1254+1 & res=v_int_14_1183' & 
x'=1 & lengthpost_1176(p_1222) --> lengthpost_1176(x).

 termAssume x'=null & x'=x & v_bool_13_1184' & x'=null & v_bool_13_1184' & 
v_int_13_1177'=0 & res=v_int_13_1177' & (((x=1 & 1<=n) | (x=null & 
n=0))) --> lengthpost_1176(x).

 termAssume n=1+n1_1223 & x'!=null & x'=x & !(v_bool_13_1184') & x'!=null & 
!(v_bool_13_1184') & v_int_14_1182'=1 & v_node_14_1180'=p_1222 & 
n_1225=n1_1223 & (((p_1222=1 & x'=2 & 1<=n1_1223) | (x'=1 & p_1222=null & 
n1_1223=0))) & lengthpre_0(x) --> lengthpre_0(v_node_14_1180').

*/
