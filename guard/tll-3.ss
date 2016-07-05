// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
 tll<ll,lr> == self::node<D1,null,lr> & self = ll
	or self::node<l,r,D2> * l::tll<ll,z> * r::tll<z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */
 tree<> == self::node<D1,null,_>
	or self::node<l,r,D2> * l::tree<> * r::tree<>
	inv self!=null;

H3<t_1026> == self::node<left,right,next>@M * left::H3<ll> 
     * right::H3<t_1026> &right!=null
 or self::node<left,right,next>@M &right=null
   inv self!=null;

G3<res_1031,t_1032> == 
 self::node<left,right,t_1032> & right=null & res_1031=self
 or self::node<left,right,next>@M * right::G3<l,t_1032> 
  * left::G3<res_1031,l>&right!=null
  inv self!=null;

H4<> == self::node<left,right,next>@M * left::H4<> 
  * right::H4<> &right!=null 
  or self::node<left,right,next>@M & right=null
   inv self!=null;


G4<res_1031,t_1032> == 
 self::node<left,right,t_1032> & right=null & res_1031=self
 or self::node<left,right,next>@M * right::G4<l,t_1032> 
  * left::G4<res_1031,l> &right!=null
  inv self!=null;

/*
pred_prim HP5<> inv true;
pred_prim HP8<> inv true;
ERROR: at tll-2.ss_47:19_47:30 
Message: UNIFICATION ERROR : at location {(47,19),(47,30)} types node and HP5 are inconsistent
 
ERROR: at tll-2.ss_47:19_47:30 
Message: gather_type_info_var : unexpected exception Failure("UNIFICATION ERROR : at location {(47,19),(47,30)} types node and HP5 are inconsistent")
 Stop Omega... 1 invocations caught
(Program not linked with -g, cannot print stack backtrace)

HP5<> == self=null or self::node<a,b,c>;
HP8<> == self=null or self::node<a,b,c>;

HP5<> == true;
HP8<> == true;

*/

// why below cause time-out?
HP5<> == self::node<a,b,c>;
HP8<> == self::node<a,b,c>;


H5<> == self::node<left,right,next>@M * left::H5<> 
  * right::H5<>  * next::HP5<> &right!=null
  or self::node<left,right,next>@M * left::HP8<> * next::HP5<> & right=null
   inv self!=null;

G5<res_1031,t_1032> == 
 self::node<left,right,t_1032> * left::HP8<> & right=null & res_1031=self
 or self::node<left,right,next>@M * right::G5<l,t_1032> 
  * left::G5<res_1031,l> * next::HP5<> &right!=null
  inv self!=null;

/*
 H(x_1025,t_1026) ::= 
 x_1025::node<left,right,next>@M * H(left,l') * H(right,t_1026) * 
 H54(next,t_1026)&right!=null
 or x_1025::node<left,right,next>@M * H84(left,t_1026) * 
    H54(next,t_1026)&right=null
 ,
 G(x_1030,res_1031,t_1032) ::= 
 x_1030::node<left,right,t_1032>@M * H84(left,t)&right=null & 
 res_1031=x_1030
 or H54(next,t_1032) * x_1030::node<left,right,next>@M * 
    G(right,l,t_1032) * G(left,res_1031,l)&right!=null
 ,
 H54(next_31_951,t) ::= NONE,
 H84(left_31_949,t) ::= NONE]
*/

// initializes the linked list fields

HeapPred H(node a, node@NI b).
HeapPred G(node a, node@NI b, node c).

node set_right (node x, node t)
//infer [H,G] requires H(x,t) ensures G(x,res,t);
                            //requires x::tree<> ensures x::tll<res,t>;
//requires x::H3<t> ensures x::G3<res,t>;
//requires x::H4<> ensures x::G4<res,t>;
requires x::H5<> ensures x::G5<res,t>;
{
  //node xr = x.right;
  //node xl = x.left;
  if (x.right==null) 
  	{
//		assert xl'=null;
  	  	x.next = t;
  	  	return x;
  	}
  else 
  	{
//		assert xr'!=null & xl'!=null;
  		node l_most = set_right(x.right, t);
  		return set_right(x.left, l_most);  		
  	}
}

/*
# tll.ss --sa-dnc --pred-en-dangling --pred-en-eup


RELASSUME
=========
[ H_8(left_29_845,r@NI) * H_9(right_29_846,r@NI) * 
  x::node<left_29_845,right_29_846,r>@M&res=x & 
  right_29_846=null --> G(x,res@NI,r),
 H(x,r@NI) --> x::node<left_29_845,right_29_846,next_29_847>@M * 
  H_8(left_29_845,r@NI) * H_9(right_29_846,r@NI) * 
  H_0(next_29_847,r@NI),
 H_9(right_29_846,r@NI)&right_29_846!=null --> H(right_29_846,r@NI),
 H_8(left_29_845,r@NI) --> H(left_29_845,l_47'@NI),
 H_0(next_29_847,r@NI) * 
  x::node<left_29_845,right_29_846,next_29_847>@M * 
  G(right_29_846,l_878@NI,r) * G(left_29_845,res@NI,l_878)&
  right_29_846!=null --> G(x,res@NI,r)]

[ // BIND
(0)H(x',t@NI)&t=t' --> x'::node<left_31_900',right_31_901',next_31_902'>@M *
HP_935(left_31_900',t@NI) * HP_936(right_31_901',t@NI) *
HP_937(next_31_902',t@NI),
 // PRE_REC
(2;0)HP_936(v_node_40_910',t'@NI)&
v_node_40_910'!=null --> H(v_node_40_910',t'@NI),
 // PRE_REC
(2;0)HP_935(v_node_41_914',t@NI)&
t=t' --> H(v_node_41_914',l_47'@NI),
 // POST
(1;0)HP_935(left_31_939,t@NI) * HP_936(right_31_940,t@NI) *
x::node<left_31_939,right_31_940,t>@M&right_31_940=null & res=t &
res=x --> G(x,res@NI,t),
 // POST
(2;0)HP_937(next_31_941,t@NI) *
x::node<left_31_939,right_31_940,next_31_941>@M *
G(right_31_940,l_969@NI,t) * G(left_31_939,res@NI,l_969)&
right_31_940!=null --> G(x,res@NI,t)]


RELDEFN
=======

[ H(x_879,r_880) ::= 
   x_879::node<__DP_8,right_29_846,__DP_0>@M&right_29_846=null
   \/  x_879::node<left_29_845,right_29_846,__DP_0>@M * H(left_29_845,l_886) 
       * H(right_29_846,r_880)&right_29_846!=null,

 G(x_883,res_884,r_885) ::= 
   res_884::node<__DP_8,right_29_846,r_885>@M&right_29_846=null & res_884=x_883
   \/  x_883::node<left_29_845,right_29_846,__DP_0>@M * G(right_29_846,l_878,r_885) 
       * G(left_29_845,res_884,l_878)&right_29_846!=null]


 G(x_993,res_994,t_995) ::=
 HP_937(next_31_941,t_995) *
 x_993::node<left_31_939,right_31_940,next_31_941>@M *
 G(right_31_940,l_969,t_995) * G(left_31_939,res_994,l_969)&
 right_31_940!=null
 or x_993::node<left_31_939,right_31_940,t_995>@M * H(left_31_939,l_992)&
    res_994=t_995 & res_994=x_993 & right_31_940=null
 ,
 H(x_987,t_988) ::= H(left_31_972,l_47') *
x_987::node<left_31_972,right_31_973,next_31_974>@M *
HP_936(right_31_973,t_988) * HP_937(next_31_974,t_988),
 HP_936(v_node_40_990,t_991) ::=
 emp&v_node_40_990=null
 or H(left_31_972,l_47') *
    v_node_40_990::node<left_31_972,right_31_973,next_31_974>@M *
    HP_936(right_31_973,t_991) * HP_937(next_31_974,t_991)
 ,
 HP_937(next_31_902',t) ::= NONE]


# tll.ss --sa-dnc


 H_8(left_29_845,r) ::= UNKNOWN,

 H(x_879,r_880) ::= 
   x_879::node<left_29_845,right_29_846,next_29_847>@M * 
       H_8(left_29_845,r_880) * H_0(next_29_847,r_880)&right_29_846=null
   \/  x_879::node<left_29_845,right_29_846,next_29_847>@M * H_0(next_29_847,r_880) 
       * H(left_29_845,l_886) * H(right_29_846,r_880)& right_29_846!=null,


 G(x_883,res_884,r_885) ::= 
   H_8(left_29_845,r_885) * res_884::node<left_29_845,right_29_846,r_885>@M
            &right_29_846=null & res_884=x_883
   \/  H_0(next_29_847,r_885) * x_883::node<left_29_845,right_29_846,next_29_847>@M 
       * G(right_29_846,l_878,r_885) * G(left_29_845,res_884,l_878)&right_29_846!=null,

 H_0(next_29_847,r) ::= UNKNOWN \/ UNKNOWN]



 G(x_993,res_994,t_995) ::=(2;0) x_993::node<left_31_939,right_31_940,__DP_HP_937>@M *
G(right_31_940,l_969,t_995) * G(left_31_939,res_994,l_969)&right_31_940!=null
   \/ (1;0) res_994::node<__DP_HP_935,right_31_940,res_994>@M&res_994=t_995 &
res_994=x_993 & right_31_940=null,
 H(x_990,t_991) ::=(2;0) H(left_31_980,l_47') *
x_990::node<left_31_980,right_31_981,__DP_HP_937>@M *
HP_936(right_31_981,t_991)
   \/ (1;0) x_990::node<__DP_HP_935,right_31_901',__DP_HP_937'>@M *
HP_936(right_31_901',t_991),
 HP_936(v_node_40_970,t_971) ::=(2;0) H(v_node_40_970,t_971)&v_node_40_970!=null
   \/ (1;0) emp&v_node_40_970=null]


=========================


 H(x,r@NI) --> x::node<left_29_845,right_29_846,next_29_847>@M * 
    H_8(left_29_845,r@NI) * H_9(right_29_846,r@NI) 
    * H_0(next_29_847,r@NI),

 H_9(right_29_846,r@NI)&right_29_846!=null --> H(right_29_846,r@NI),

 H_8(left_29_845,r@NI) --> H(left_29_845,l_47'@NI),

 H_0(next_29_847,r@NI) --> emp,

 H_9(right_29_846,r@NI)&right_29_846=null --> emp,

------

 H_8(left_29_845,r@NI) * x::node<left_29_845,right_29_846,r>@M&res=x & 
  right_29_846=null --> G(x,r@NI,res),

 H_0(next_29_847,r@NI) * 
  x::node<left_29_845,right_29_846,next_29_847>@M * 
  G(right_29_846,r@NI,l_878) * G(left_29_845,l_878@NI,res)&
  right_29_846!=null --> G(x,r@NI,res)]
-------
[ H(x,r@NI) --> x::node<left_29_845,right_29_846,next_29_847>@M * 
  H_8(left_29_845,r@NI) * H_9(right_29_846,r@NI) * 
  H_0(next_29_847,r@NI),

 H_9(right_29_846,r@NI)&right_29_846!=null --> H(right_29_846,r@NI),

 H_8(left_29_845,r@NI) --> H(left_29_845,l_47'@NI),

 H_0(next_29_847,r@NI) --> emp,

 H_9(right_29_846,r@NI)&right_29_846=null --> emp,

 H_8(left_29_845,r@NI) * x::node<left_29_845,right_29_846,r>@M&res=x & 
  right_29_846=null --> G(x,r@NI,res),

 H_0(next_29_847,r@NI) * 
  x::node<left_29_845,right_29_846,next_29_847>@M * 
  G(right_29_846,r@NI,l_878) * G(left_29_845,l_878@NI,res)&
  right_29_846!=null --> G(x,r@NI,res)]

-------
 H(x_899,r_900) ::=  x_899::node<left_29_845,right_29_846,next_29_847>@M 
  * H_8(left_29_845,r_900) * H_9(right_29_846,r_900) 
  * H_0(next_29_847,r_900),

 G(x_901,r_902,res_903) ::=  
 H_0(next_29_847,r_902) * 
 x_901::node<left_29_845,right_29_846,next_29_847>@M * 
 G(right_29_846,r_902,l_878) * G(left_29_845,l_878,res_903)&
 right_29_846!=null
 or H_8(left_29_845,r_902) * 
    x_901::node<left_29_845,right_29_846,r_902>@M&right_29_846=null & 
    res_903=x_901,

 H_9(right_29_895,r_896) ::=  
 left_29_890::node<left_29_845,right_29_846,next_29_847>@M * 
 H_8(left_29_845,l_881) * H_9(right_29_846,l_881) * 
 H_0(next_29_847,l_881) * 
 right_29_895::node<left_29_890,right_29_891,next_29_892>@M * 
 H_9(right_29_891,r_896) * H_0(next_29_892,r_896)
 or emp&right_29_895=null,

 H_8(left_29_897,r_898) ::=  left_29_897::node<left_29_845,right_29_846,next_29_847>@M * 
 H_8(left_29_845,l_881) * H_9(right_29_846,l_881) * H_0(next_29_847,l_881),

 H_0(next_29_847,r) ::= NONE]





*/
