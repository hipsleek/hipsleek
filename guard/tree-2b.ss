// simpler tll working example
data node{
  node left;
  node right;
}

tree<> == self::node<_,null>
      or self::node<l,r> * l::tree<> * r::tree<>
	inv self!=null;

gtree<> == self=null 
      or self::node<l,r> * l::gtree<> * r::gtree<>
	inv true;

// initializes the linked list fields

void trav (node x)
//infer [H,G] requires H(p,x) ensures G(p,x);
//requires x::tree<p>  ensures x::tree<p>;
requires x::gtree<>  ensures x::gtree<>;
{
  node xr = x.right;
}

