// tll with parent working example

data node{
	node parent;
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree  */
tree<p> == self::node<p,D1,null,_>
  or self::node<p,l,r,D2> * l::tree<self> * r::tree<self>
	inv self!=null;

/* predicate for a non-empty tree with chained leaf list */
tll<p,ll,lr> == self::node<p,D1,null,lr> & self = ll
    or self::node<p,l,r,D2> * l::tll<self,ll,z> * r::tll<self,z,lr>
	inv self!=null;

node set_right (node p, node x, node t)
  requires x::tree<p> 
  ensures x::tll<p,res,t>;
{
  node xr = x.right;
  node xl = x.left;
  node pp = x.parent;
  //assert pp'=p;
  // dprint;
  if (x.right==null) 
  	{
                //assert xl'=null;
  	  	x.next = t;
  	  	return x;
  	}
  else 
  	{
          //assert xr'!=null & xl'!=null;
          node l_most = set_right(x,x.right, t);
          return set_right(x,x.left, l_most);  		
  	}
}

/*
Add size property to show that the number of
nodes is being preserved by this method.



*/
