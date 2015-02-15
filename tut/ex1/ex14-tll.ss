// tll with parent working example

data node4{
	node4 parent;
	node4 left;
	node4 right;
	node4 next;
}

/* predicate for a non-empty tree with chained leaf list */
tll<p,ll,lr> == self::node4<p,D1,null,lr> & self = ll
    or self::node4<p,l,r,D2> * l::tll<self,ll,z> * r::tll<self,z,lr>
	inv self!=null;

/* predicate for a non-empty tree  */
tree<p> == self::node4<p,D1,null,_>
  or self::node4<p,l,r,D2> * l::tree<self> * r::tree<self>
	inv self!=null;

node4 set_right (node4 p, node4 x, node4 t)
  requires x::tree<p> 
  ensures x::tll<p,res,t>;
{
  node4 xr = x.right;
  node4 xl = x.left;
  node4 pp = x.parent;
  //assert pp'=p;
  // dprint;
  if (x.right==null) {
    assert xl'=null;
    x.next = t;
    return x;
  }
  else{
    assert xr'!=null & xl'!=null;
    node4 l_most = set_right(x,x.right, t);
    return set_right(x,x.left, l_most);
  }
}

