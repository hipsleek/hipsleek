// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */

Iosif spec
==========
 tree<> == self::node<null,null,_>
	or self::node<l,r,null> * l::tree<> * r::tree<>
	inv self!=null;

 tll<ll,lr> == self::node<null,null,lr> & self = ll
	or self::node<l,r,null> * l::tll<ll,z> * r::tll<z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */

Our stronger spec
=================
 tree2<> == self::node<_,null,_> 
	or self::node<l,r,null> * l::tree2<> * r::tree2<>
	inv self!=null;

 tll2<ll,lr> == self::node<_,null,lr> & self=ll
	or self::node<l,r,null> * l::tll2<ll,z> * r::tll2<z,lr>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node a, node@NI b).
HeapPred G(node a, node@NI b, node c).

node set_right (node x, node r)
//infer [H,G] requires H(x,r) ensures G(x,r,res);
//requires x::tree<> ensures x::tll<res,r>;
requires x::tree2<> ensures x::tll2<res,r>;
// fail as right!=null --> left!=null
{
  if (x.right==null) 
  	{
  	  	x.next = r;
  	  	return x;
  	}
  else 
  	{
  		node l_most = set_right(x.right, r);
  		return set_right(x.left, l_most);  		
  	}
}

/*
# tll.ss

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
  HP_848(left_29_845,r@NI) * HP_849(right_29_846,r@NI) * 
  HP_850(next_29_847,r@NI),

 HP_849(right_29_846,r@NI)&right_29_846!=null --> H(right_29_846,r@NI),

 HP_848(left_29_845,r@NI) --> H(left_29_845,l_47'@NI),

 HP_850(next_29_847,r@NI) --> emp,

 HP_849(right_29_846,r@NI)&right_29_846=null --> emp,

 HP_848(left_29_845,r@NI) * x::node<left_29_845,right_29_846,r>@M&res=x & 
  right_29_846=null --> G(x,r@NI,res),

 HP_850(next_29_847,r@NI) * 
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