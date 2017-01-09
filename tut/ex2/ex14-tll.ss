// tll with parent working example

data node{
	node parent;
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree  */
tree<> == self::node<_,D1,null,_>
  or self::node<_,l,r,D2> * l::tree<> * r::tree<> & r!=null
	inv self!=null;

/* predicate for a non-empty tree with chained leaf list */
tll<p,ll,lr> == self::node<p,D1,null,lr> & self = ll
    or self::node<p,l,r,D2> * l::tll<self,ll,z> * r::tll<self,z,lr> & r!=null
	inv self!=null;


// initializes the linked list fields
  HeapPred H(node a, node@NI p, node@NI b).
  HeapPred G(node a, node p, node b, node c).

node set_right (node p, node x, node t)
  infer [H,G] 
  requires H(x,p,t) 
  ensures G(x,p,res,t) ;

  // requires x::tree<> ensures x::tll<p,res,t>;
{
  x.parent=p;
  if (x.right==null){
    x.next = t;
    return x;
  }
  else{
    node l_most = set_right(x,x.right, t);
    return set_right(x,x.left, l_most);
  }
}

/*
# ex14-tll.ss

How come G no longer proved to be equiv to tll?
Your engine is not using syn mode..

[ H(x_1604,p_1605,t_1606) ::= x_1604::tree<>(4,5),
 G(x_1608,p_1609,res_1610,t_1611) ::= 
    x_1608::node<p_1609,left_32_1498,right_34_1539,t_1611> * 
    left_32_1498::tree<>&right_34_1539=null & x_1608=res_1610
 or x_1608::node<p_1609,DP_DP_DP_1541,right_34_1539,t_1611>&
    right_34_1539=null & x_1608=res_1610
 or x_1608::node<p_1609,left_32_1498,right_34_1539,DP_DP_HP_1504> * 
    G(right_34_1539,x_1608,l_1540,t_1611) * 
    G(left_32_1498,x_1608,res_1610,l_1540)&right_34_1539!=null
 (4,5)]


*/
