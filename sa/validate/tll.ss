// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
 tll<ll,lr> == self::node<null,null,lr> & self = ll
	or self::node<l,r,null> * l::tll<ll,z> * r::tll<z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */
 tree<> == self::node<null,null,_>
	or self::node<l,r,null> * l::tree<> * r::tree<>
	inv self!=null;


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
