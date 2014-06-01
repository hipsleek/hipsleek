// tll with parent

data node{
  node parent;
  node left;
  node right;
  node next;
}

/* predicate for a non-empty tree  */
tree<> == (exists p, D1, r, n: self::node<p,D1,r,n> & r=null)
  or (exists p,l,r,D2: self::node<p,l,r,D2> * l::tree<> * r::tree<> & r!=null)
	inv self!=null;

/* predicate for a non-empty tree with chained leaf list */
tll<p,ll,lr> == (exists p,D1, l : self::node<p,D1,l,lr> & l=null & self = ll)
  or (exists l,r,D2,z : self::node<p,l,r,D2> * l::tll<self,ll,z> * r::tll<self,z,lr> & r!=null)
	inv self!=null;



node set_right (node p, node x, node t)
  requires x::tree<> ensures x::tll<p,res,t>;
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

