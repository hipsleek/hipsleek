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
//infer [H,G] requires H(x,t) ensures G(x,res,t);
requires x::tree<> ensures x::tll<res,t>;
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

bool check_tll(node x,node t, node@R r)
//  infer [H,G] requires H(x,t,r) ensures G(x,t,r) & res;//'
  requires x::tll<t,ggg> ensures x::tll<t,ggg> & res & r'=ggg;//'
{
  if (x.right==null && x.left==null)
    {
      r = x.next;
      return true;
    }
  else
    {
      if (x.left==null || x.right==null ) return false;
      node r_most;
      bool b = check_tll(x.left, t, r_most);
      return b && check_tll(x.right, r_most, r);
    }
}

