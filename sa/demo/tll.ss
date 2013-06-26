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

node set_right (node x, node r)
infer [H,G] requires H(x,r) ensures G(x,r,res);
//requires x::tree<> ensures x::tll<res,r>;
{
  if (x.right==null) 
  	{
  	  	x.next = r;
  	  	return x;
  	}
  else 
  	{
  		node l_most = set_right(x.right, r);
  		return set_right(x.left, l_most);  		
  	}
}

/*
[ 
  H(x,r)&true --> x::node<left_29_845,right_29_846,next_29_847>@M * 
  HP_8(left_29_845,r) * HP_9(right_29_846,r) * 
  HP_0(next_29_847,r).

  HP_9(right_29_846,r)&right_29_846!=null --> H(right_29_846,r).
 
  HP_8(left_29_845,r)&true --> H(left_29_845,l_47').
 
  HP_9(right_29_846,r)&right_29_846=null --> emp.

 HP_8(left_29_845,r) * x::node<left_29_845,right_29_846,r>@M&res=x & 
  right_29_846=null --> G(x,r,res).

 HP_0(next_29_847,r) * 
  x::node<left_29_845,right_29_846,next_29_847>@M * 
  G(right_29_846,r,l_878) * G(left_29_845,l_878,res)&
  right_29_846!=null --> G(x,r,res).
*/