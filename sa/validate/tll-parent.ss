// simpler tll working example

data node{
	node parent;
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
tll<p,ll,lr> == self::node<p,null,null,lr> & self = ll
  or self::node<p,l,r,null> * l::tll<self,ll,z> * r::tll<self,z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */
tree<p> == self::node<p,null,null,_>
        or self::node<p,l,r,null> * l::tree<self> * r::tree<self>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node@NI p, node a, node@NI b).
HeapPred G(node@NI p, node a, node@NI b, node c).

node set_right (node p, node x, node t)
  infer [H,G] requires H(p,x,t) ensures G(p,x,res,t);
  //requires x::tree<p> ensures x::tll<p,res,t>;
{
x.parent=p;
dprint;
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
# tll.ss --sa-dnc --pred-en-dangling --pred-en-eup


[ G(p_1089,x_1090,res_1091,t_1092) ::=(2;0) HP_1008(parent_32_1004,p_1089,t_1092) * 
HP_1011(next_32_1007,p_1089,t_1092) * 
x_1090::node<parent_32_1004,left_32_1005,right_32_1006,next_32_1007>@M * 
G(x_1090,right_32_1006,l_1048,t_1092) * 
G(x_1090,left_32_1005,res_1091,l_1048)&right_32_1006!=null
   \/ (1;0) HP_1008(parent_32_1004,p_1089,t_1092) * 
HP_1009(left_32_1005,p_1089,t_1092) * 
x_1090::node<parent_32_1004,left_32_1005,right_32_1006,t_1092>@M&
res_1091=x_1090 & right_32_1006=null,
 H(p_1085,x_1086,t_1087) ::=(2;0) H(x_1086,left_32_1053,l_56') * 
x_1086::node<parent_32_1052,left_32_1053,right_32_1054,next_32_1055>@M&
right_32_1054!=null
   \/ (1;0) x_1086::node<parent_32_1004,left_32_1005,right_32_1006,next_32_1007>@M * 
HP_1008(parent_32_1004,p_1085,t_1087) * 
HP_1009(left_32_1005,p_1085,t_1087) * HP_1011(next_32_1007,p_1085,t_1087)&
right_32_1006=null,
 HP_1008(parent_32_1004,p,t) ::= htrue,
 HP_1009(left_32_1082,p_1083,t_1084) |#| x::node<parent_32_1004,left_32_1005,right_32_1006,next_32_1007>@M ::=
  (2;0) H(left_32_1082,left_32_1053,l_56') * 
left_32_1082::node<parent_32_1052,left_32_1053,right_32_1054,next_32_1055>@M&
right_32_1054!=null
   \/ (1;0) NONE,
 HP_1011(next_32_1007,p,t) ::= htrue]


[ // BIND
(0)H(p@NI,x,t@NI) --> x::node<parent_32_1004,left_32_1005,right_32_1006,next_32_1007>@M * 
HP_1008(parent_32_1004,p@NI,t@NI) * HP_1009(left_32_1005,p@NI,t@NI) * 
HP_1010(right_32_1006,p@NI,t@NI) * 
HP_1011(next_32_1007,p@NI,t@NI),
 // PRE_REC
(2;0)HP_1010(right_32_1006,p@NI,t@NI)&
right_32_1006!=null |#| x::node<parent_32_1004,left_32_1005,right_32_1006,next_32_1007>@M --> H(x@NI,right_32_1006,t@NI),
 // PRE_REC
(2;0)HP_1009(left_32_1005,p@NI,t@NI) |#| x::node<parent_32_1004,left_32_1005,right_32_1006,next_32_1007>@M --> H(x@NI,left_32_1005,l_56'@NI),
 // POST
(1;0)HP_1008(parent_32_1004,p@NI,t@NI) * HP_1009(left_32_1005,p@NI,t@NI) * 
HP_1010(right_32_1006,p@NI,t@NI) * 
res::node<parent_32_1004,left_32_1005,right_32_1006,t>@M&
right_32_1006=null & 
res=x --> G(p@NI,x,res@NI,t),
 // POST
(2;0)HP_1008(parent_32_1004,p@NI,t@NI) * HP_1011(next_32_1007,p@NI,t@NI) * 
x::node<parent_32_1004,left_32_1005,right_32_1006,next_32_1007>@M * 
G(x@NI,right_32_1006,l_1048@NI,t) * G(x@NI,left_32_1005,res@NI,l_1048)&
right_32_1006!=null --> G(p@NI,x,res@NI,t)]

*/
