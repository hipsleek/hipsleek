// simpler tll working example

data node{
	node left;
	node right;
	node next;
}

/* predicate for a non-empty tree with chained leaf list */
 tll<ll,lr> == self=null & ll=lr 
    or self::node<null,null,lr> & self = ll
	or self::node<l,r,null> * l::tll<ll,z> * r::tll<z,lr>;
	//inv self!=null;

/* predicate for a non-empty tree  */
 tree<> == self = null //self::node<null,null,_>
	or self::node<l,r,null> * l::tree<> * r::tree<>;
	//inv self!=null;


// initializes the linked list fields

HeapPred H(node a, node b).
HeapPred G(node a, node b, node c).

node set_right (node x, node r)
//infer [H,G] requires H(x,r) ensures G(x,r,res);
requires x::tree<>&x!=null ensures x::tll<res,r>;
{ 
 if (x.right==null) 
  	if (x.left == null)
	{
  	  	x.next = r;
  	  	return x;
  	}
	else return set_right(x.left, r);
  else 
  	{
  		node l_most = set_right(x.right, r);
  		if (x.left==null) return l_most;
		else return set_right(x.left, l_most);  		
  	}
}
