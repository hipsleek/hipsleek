// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
 tll<ll,lr> == self::node<_,null,lr> & self = ll
  or self::node<l,r,_> * l::tll<ll,z> * r::tll<z,lr> //& r!=null
	inv self!=null;

/* predicate for a non-empty tree  */
 tree<> == self::node<_,null,_>
	or self::node<l,r,_> * l::tree<> * r::tree<>
	inv self!=null;

/*
 GG<rr,t> == self::node<DP1,right,t> & right=null & rr=self
   or self::node<left,right,DP> * left::GG<rr,l>
         * right::GG<l,t> & right!=null
   inv true;
*/

//lemma_safe self::tll<a,b> <-> self::GG<a,b>;

// initializes the linked list fields

HeapPred H(node a, node@NI b).
HeapPred G(node a, node@NI b, node c).

node set_right (node x, node t)
infer [H,G] requires H(x,t) ensures G(x,res,t);
//requires x::tree<> ensures x::tll<res,t>;
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
# tll.ss

Why isn't -dre "check_.*coercion" below called?

check_left_coercion@1
check_left_coercion inp1 :Lemma "lem_16":  self::tll<a,b>@M&{FLOW,(24,25)=__norm}[]==> self::GG<a,b>@M&{FLOW,(24,25)=__norm}[]
 head match:tll
 body view:GG

check_right_coercion@3
check_right_coercion inp1 :Lemma "lem_16":  self::tll<a,b>@M&{FLOW,(24,25)=__norm}[]<== self::GG<a,b>@M&{FLOW,(24,25)=__norm}[]
 head match:tll
 body view:GG


# tll.ss --pred-en-equiv --pred-en-useless-para --pred-en-dangling

Why isn't predicate reuse working at all?

[ H(x,t) ::= HP_1123(x),
 G(x,res,t) ::= 
 x::node&lt;DP1,right,t&gt;@M&right=null & res=x
 or x::node&lt;left,right,DP&gt;@M * G(left,res,l) * G(right,l,t)&right!=null
 ,
 HP_1123(x) ::= 
 x::node&lt;left,right,DP&gt;@M * HP_1123(left) * HP_1123(right)&right!=null
 or x::node&lt;DP1,right,DP&gt;@M&right=null
 ]


# tll.ss 

hip produced:

[ H(x,t) ::= 
 x::node<left,right,next>@M * H(left,l') * H(right,t) * HP_958(next,t)&
 right!=null
 or x::node<left,right,next>@M * DP_1044(left,t) * HP_958(next,t)&right=null
 ,
 G(x,res,t1) ::= 
 x::node<left,right,t1>@M * DP_1044(left,t)&right=null & res=x
 or x::node<left,right,next>@M * G(left,res,l) * G(right,l,t1) * 
    HP_958(next,t1)&right!=null
 ,
 DP_1044(left,t) ::= NONE,
 HP_958(next,t) ::= NONE]

However, 
 generating sleek file : logs/mod_tll.slk
produced:


[ H(x,t) ::= 
 x::node<left,right,next>@M * H(left,l') * H(right,t) * HP_958(next,t)&
 right!=null
 or x::node<left,right,next>@M * DP_89(left,t) * HP_958(next,t)&right=null,

 G(x,res,t1) ::= 
 x::node<left,right,t1>@M * DP_89(left,t)&right=null & res=x
 or x::node<left,right,next>@M * G(left,res,l) * G(right,l,t1) * 
    HP_958(next,t1)&right!=null
 ,
 DP_89(left,t) ::= NONE,
 HP_958(next,t) ::= NONE]


Why do we print these intermediates? their definitions
look odd (seems incorrect).

 HP_956(left1,t) |#| 
                     res::node<left_31_90,right_31_954,t_91>@M&
                     right_31_954=null
                     or x::node<left_31_90,right_31_954,next_31_955>@M&
                        right_31_954!=null
                      ::= 
 DP_89(left,t1)
 or H(left1,l'),

 HP_957(right,t) ::= 
 H(right,t)&right!=null
 or emp&right=null,
*************************************




 tll<res,tt> == self::node<_,null,tt> & self = res
	or self::node<l,r,_> * l::tll<res,z> * r::tll<z,tt>
	inv self!=null;

[ H(x,t) ::=x::tree<>@M,
 G(x,res,t) ::= 
 x::node<DP1,right,t>@M&right=null & res=x
 or x::node<left,right,DP>@M * G(left,res,l) * G(right,l,t)&right!=null
 ]

================================

This spurious message came from below. They don't look
correct, and should also be omitted.

../sleek logs/mod_tll.slk

 HP_956(left,t1) |#| 
                     res::node<left_31_90,right_31_954,t_91>@M&
                     right_31_954=null
                     or x::node<left_31_90,right_31_954,next_31_955>@M&
                        right_31_954!=null
                      ::= 
 DP_89(left1,t)
 or H(left,l'),
 HP_957(right,t) ::= 
 H(right,t)&right!=null
 or emp&right=null


=============================
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
