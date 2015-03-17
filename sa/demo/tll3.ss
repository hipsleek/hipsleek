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
infer [H,G] requires H(x,r) ensures G(x,r,res);
//requires x::tree<>&x!=null ensures x::tll<res,r>;
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

/*
[ H(x,r)&true --> x::node<left_30_851,right_30_852,next_30_853>@M * HP_854(left_30_851,r@NI) * HP_855(right_30_852,r@NI) * 
  HP_856(next_30_853,r@NI) * HP_857(r,x@NI)&true,

 HP_855(right_30_852,r@NI)&right_30_852=null --> emp&true,

 HP_854(left_30_851,r@NI) * HP_857(r,x@NI)&left_30_851!=null &  right_30_852=null --> H(left_30_851,r)&true,
 HP_855(right_30_852,r@NI) * HP_857(r,x@NI)& right_30_852!=null --> H(right_30_852,r)&true,

  HP_855(right_30_852,r@NI)&right_30_852=null --> emp&true,
 HP_854(left_30_851,r@NI)&left_30_851=null --> emp&true,
 HP_857(r,x@NI) * x::node<left_30_851,right_30_852,r>@M&res=x & right_30_852=null & left_30_851=null --> G(x,r,res)&true,
HP_854(left_30_851,r@NI)&left_30_851=null --> emp&true,

HP_854(left_30_851,r@NI) * G(right_30_852,r,l_42')&right_30_852!=null & 
  left_30_851!=null --> H(left_30_851,l_42') * HP_908(right_30_852,r)&true,
HP_856(next_30_853,r@NI) *  x::node<left_30_851,right_30_852,next_30_853>@M * G(left_30_851,r,res)&
  left_30_851!=null & right_30_852=null --> G(x,r,res)&true,

  HP_856(next_30_853,r@NI) * x::node<left_30_851,right_30_852,next_30_853>@M * G(right_30_852,r,res)&
  right_30_852!=null & left_30_851=null --> G(x,r,res)&true,
 HP_856(next_30_853,r@NI) * 
  x::node<left_30_851,right_30_852,next_30_853>@M * 
  G(right_30_852,r,l_911) * HP_908(right_30_852,r) * 
  G(left_30_851,l_911,res)&right_30_852!=null & 
  left_30_851!=null --> G(x,r,res)&true]

 */
