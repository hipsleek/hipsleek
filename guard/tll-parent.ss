// tll with parent working example

data node{
	node parent;
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
tll<p,ll,lr> == self::node<p,D1,null,lr> & self = ll
    or self::node<p,l,r,D2> * l::tll<self,ll,z> * r::tll<self,z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */
tree<p> == self::node<p,D1,null,_>
  or self::node<p,l,r,D2> * l::tree<self> * r::tree<self>
	inv self!=null;

// initializes the linked list fields

  HeapPred H(node a, node@NI p, node@NI b).
  HeapPred G(node a, node@NI p, node@NI b, node@NI c).

node set_right (node p, node x, node t)
  infer [H,G] 
  requires H(x,p,t) 
  ensures G(x,p,res,t) ;
  //requires x::tree<p> ensures x::tll<p,res,t>;
{
  //node xr = x.right;
  //node xl = x.left;
  node pp = x.parent;
  assert pp'=p assume pp'=p;
  // dprint;
  if (x.right==null) 
  	{
//		assert xl'=null;
  	  	x.next = t;
  	  	return x;
  	}
  else 
  	{
//		assert xr'!=null & xl'!=null;
          node l_most = set_right(x,x.right, t);
          return set_right(x,x.left, l_most);  		
  	}
}

/*
# tll-parent.ss --pred-en-dangling

[ G(x_1090,p_1091,res_1092,t_1093) ::= 
 x_1090::node<p_1091,left_34_994,right_34_995,__DP_HP_1000>@M * 
 G(right_34_995,x_1090,l_1037,t_1093) * 
 G(left_34_994,x_1090,res_1092,l_1037)&right_34_995!=null
 or x_1090::node<p_1091,left_34_994,right_34_995,t_1093>@M * 
    H(left_34_994,x_1088,l_1089)&res_1092=x_1090 & right_34_995=null
 ,
 H(x_1084,p_1085,t_1086) ::= 
 H(left_34_1071,x_1084,l_48') * 
 x_1084::node<parent_34_1074,left_34_1071,right_34_1072,__DP_HP_1000>@M * 
 H(right_34_1072,x_1084,t_1086)&right_34_1072!=null & p_1085=parent_34_1074
 or H(left_34_1071,x_1084,l_48') * 
    x_1084::node<parent_34_1074,left_34_1071,right_34_1072,__DP_HP_1000>@M&
    right_34_1072=null & p_1085=parent_34_1074
 ]

[ // BIND
(0)H(x,p@NI,t@NI) --> x::node<parent_34_993,left_34_994,right_34_995,next_34_996>@M * 
HP_997(parent_34_993,p@NI,t@NI) * HP_998(left_34_994,p@NI,t@NI) * 
HP_999(right_34_995,p@NI,t@NI) * 
HP_1000(next_34_996,p@NI,t@NI),
 // Assert
(0)HP_997(parent_34_993,p@NI,t@NI) --> emp&
p=parent_34_993,
 // PRE_REC
(2;0)HP_999(right_34_995,p@NI,t@NI)&
right_34_995!=null |#| x::node<p,left_34_994,right_34_995,next_34_996>@M --> H(right_34_995,x@NI,t@NI),
 // PRE_REC
(2;0)HP_998(left_34_994,p@NI,t@NI) |#| x::node<p,left_34_994,right_34_995,next_34_996>@M&
right_34_995!=null --> H(left_34_994,x@NI,l_48'@NI),
 // POST
(1;0)HP_998(left_34_994,p@NI,t@NI) * HP_999(right_34_995,p@NI,t@NI) * 
res::node<p,left_34_994,right_34_995,t>@M&right_34_995=null & 
res=x --> G(x,p@NI,res@NI,t@NI),
 // POST
(2;0)HP_1000(next_34_996,p@NI,t@NI) * 
x::node<p,left_34_994,right_34_995,next_34_996>@M * 
G(right_34_995,x@NI,l_1037@NI,t@NI) * G(left_34_994,x@NI,res@NI,l_1037@NI)&
right_34_995!=null --> G(x,p@NI,res@NI,t@NI)]


==========================================

[ G(x_1090,p_1091,res_1092,t_1093) ::= 
 HP_1000(next_34_996,p_1091,t_1093) * 
 x_1090::node<p_1091,left_34_994,right_34_995,next_34_996>@M * 
 G(right_34_995,x_1090,l_1037,t_1093) * 
 G(left_34_994,x_1090,res_1092,l_1037)&right_34_995!=null
 or x_1090::node<p_1091,left_34_994,right_34_995,t_1093>@M * 
    H(left_34_994,x_1088,l_1089)&res_1092=x_1090 & right_34_995=null
 ,

How come HP_1000 is missing in pre-predicate?
We cannot form dangling in this scenario.

 H(x_1084,p_1085,t_1086) ::= 
 H(left_34_1072,x_1084,l_48') * 
 x_1084::node<parent_34_1074,left_34_1072,right_34_1073,next_34_1071>@M * 
 H(right_34_1073,x_1084,t_1086)&right_34_1073!=null & p_1085=parent_34_1074
 or H(left_34_1072,x_1084,l_48') * 
    x_1084::node<parent_34_1074,left_34_1072,right_34_1073,next_34_1071>@M&
    right_34_1073=null & p_1085=parent_34_1074
 ,

===========

HeapPred H7(node parent3, node@NI p, node@NI t).
HeapPred H(node a, node@NI p, node@NI b).
HeapPred H8(node left4, node@NI p, node@NI t).
HeapPred H9(node right5, node@NI p, node@NI t).
HeapPred H10(node next6, node@NI p, node@NI t).
HeapPred G(node a, node@NI p, node@NI b, node c).

[ G(x_1090,p_1091,res_1092,t_1093) ::= 
 H10(next6,p_1091,t_1093) * 
 x_1090::node<p_1091,left4,right5,next6>@M * 
 G(right5,x_1090,l_1037,t_1093) * 
 G(left4,x_1090,res_1092,l_1037)&right5!=null
 or x_1090::node<p_1091,left4,right5,t_1093>@M * 
    H(left4,x_1088,l_1089)&res_1092=x_1090 & right5=null
 ,
 H(x_1084,p_1085,t_1086) ::= 
 H(left2,x_1084,l_48') * 
 x_1084::node<parent4,left2,right3,next1>@M * 
 H(right3,x_1084,t_1086)&right3!=null & p_1085=parent4
 or H(left2,x_1084,l_48') * 
    x_1084::node<parent4,left2,right3,next1>@M&
    right3=null & p_1085=parent4
 ,






*/
