// simpler tll working example

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
  /* assert pp'=p assume pp'=p; */
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
# tll-parent-2.ss  --pred-en-dangling

[ G(x_1065,p_1066,res_1067,t_1068) ::= 
 x_1065::node<__DP_HP_991,left_34_988,right_34_989,t_1068>@M * 
 H(left_34_988,x_1063,l_1064)&res_1067=x_1065 & right_34_989=null
 or x_1065::node<__DP_HP_991,left_34_988,right_34_989,__DP_HP_994>@M * 
    G(right_34_989,x_1065,l_1031,t_1068) * 
    G(left_34_988,x_1065,res_1067,l_1031)&right_34_989!=null
 ,
 H(x_1059,p_1060,t_1061) ::= 
 H(left_34_1053,x_1059,l_48') * 
 x_1059::node<__DP_HP_991,left_34_1053,right_34_1054,__DP_HP_994>@M * 
 H(right_34_1054,x_1059,t_1061)&right_34_1054!=null
 or H(left_34_1053,x_1059,l_48') * 
    x_1059::node<__DP_HP_991,left_34_1053,right_34_1054,__DP_HP_994>@M&
    right_34_1054=null
 ]


*/
