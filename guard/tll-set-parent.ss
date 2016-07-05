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
tree<> == self::node<_,D1,null,_>
  or self::node<_,l,r,D2> * l::tree<> * r::tree<> & r!=null
	inv self!=null;

// initializes the linked list fields

  HeapPred H(node a, node@NI p, node@NI b).
  HeapPred G(node a, node@NI p, node@NI b, node@NI c).

node set_right (node p, node x, node t)
  infer [H,G] 
  requires H(x,p,t) 
  ensures G(x,p,res,t) ;
  //requires x::tree<> ensures x::tll<p,res,t>;
{
  x.parent=p;
  if (x.right==null) 
  	{
  	  	x.next = t;
  	  	return x;
  	}
  else 
  	{
          node l_most = set_right(x,x.right, t);
          return set_right(x,x.left, l_most);  		
  	}
}

/*
# tll-parent.ss --pred-en-dangling


[ G(x_1054,p_1055,res_1056,t_1057) ::= 
 x_1054::node<p_1055,left_33_978,right_33_979,__DP_HP_984>@M * 
 G(right_33_979,x_1054,l_1020,t_1057) * 
 G(left_33_978,x_1054,res_1056,l_1020)&right_33_979!=null
 or x_1054::node<p_1055,left_33_978,right_33_979,t_1057>@M * 
    H(left_33_978,x_1052,l_1053)&res_1056=x_1054 & right_33_979=null
 ,
 H(x_1048,p_1049,t_1050) ::= 
 H(left_33_1042,x_1048,l_45') * 
 x_1048::node<__DP_HP_981,left_33_1042,right_33_1043,__DP_HP_984>@M * 
 H(right_33_1043,x_1048,t_1050)&right_33_1043!=null
 or H(left_33_1042,x_1048,l_45') * 
    x_1048::node<__DP_HP_981,left_33_1042,right_33_1043,__DP_HP_984>@M&
    right_33_1043=null
 ]

==============sa-dnc

[ G(x_1045,p_1046,res_1047,t_1048) ::=(2;0) HP_1066(next_33_980,p_1046,t_1048) * 
x_1045::node<p_1046,left_33_978,right_33_979,next_33_980>@M * 
G(right_33_979,x_1045,l_1020,t_1048) * G(left_33_978,x_1045,res_1047,l_1020)&
right_33_979!=null
   \/ (1;0) HP_1068(left_33_978,p_1046,t_1048) * 
x_1045::node<p_1046,left_33_978,right_33_979,t_1048>@M&res_1047=x_1045 & 
right_33_979=null,
 H(x_1041,p_1042,t_1043) ::=(2;0) H(left_33_1035,x_1041,l_45') * 
x_1041::node<parent_33_1034,left_33_1035,right_33_1036,next_33_1037>@M * 
HP_1067(parent_33_1034,p_1042,t_1043) * 
HP_1066(next_33_1037,p_1042,t_1043) * H(right_33_1036,x_1041,t_1043)&
right_33_1036!=null
   \/ (1;0) x_1041::node<parent_33_977,left_33_978,right_33_979,next_33_980>@M * 
HP_1069(parent_33_977,p_1042,t_1043) * HP_1068(left_33_978,p_1042,t_1043) * 
HP_1070(next_33_980,p_1042,t_1043)&right_33_979=null,
 HP_1066(next_33_980,p,t) ::=(2;0) NONE,
 HP_1067(parent_33_977,p,t) ::=(2;0) NONE,
 HP_1068(left_33_978,p,t) ::=(1;0) NONE,
 HP_1069(parent_33_977,p,t) ::=(1;0) NONE,
 HP_1070(next_33_980,p,t) ::=(1;0) NONE]

*************************************
[ G(x_1054,p_1055,res_1056,t_1057) ::= 
 HP_984(next_33_980,p_1055,t_1057) * 
 x_1054::node<p_1055,left_33_978,right_33_979,next_33_980>@M * 
 G(right_33_979,x_1054,l_1020,t_1057) * 
 G(left_33_978,x_1054,res_1056,l_1020)&right_33_979!=null
 or x_1054::node<p_1055,left_33_978,right_33_979,t_1057>@M * 
    H(left_33_978,x_1052,l_1053)&res_1056=x_1054 & right_33_979=null
 ,pred
 H(x_1048,p_1049,t_1050) ::= 
 H(left_33_1042,x_1048,l_45') * 
 x_1048::node<parent_33_1041,left_33_1042,right_33_1043,next_33_1044>@M * 
 HP_981(parent_33_1041,p_1049,t_1050) * HP_984(next_33_1044,p_1049,t_1050) * 
 H(right_33_1043,x_1048,t_1050)&right_33_1043!=null
 or H(left_33_1042,x_1048,l_45') * 
    x_1048::node<parent_33_1041,left_33_1042,right_33_1043,next_33_1044>@M * 
    HP_981(parent_33_1041,p_1049,t_1050) * 
    HP_984(next_33_1044,p_1049,t_1050)&right_33_1043=null
 ,
 HP_981(parent_33_977,p,t) ::= NONE,
 HP_984(next_33_980,p,t) ::= NONE]
*************************************

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
