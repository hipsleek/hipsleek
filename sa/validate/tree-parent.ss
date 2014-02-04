// simpler tll working example

data node{
	node parent;
	node right;
        node left;
}

tree<p> == self::node<p,null,null>
  or self::node<p,r,l> * r::tree<self>* l::tree<self>
	inv self!=null;


// initializes the linked list fields

HeapPred H(node@NI p, node a).
HeapPred G(node@NI p, node a).

bool trav (node p, node x)
 infer [H,G] requires H(p,x) ensures G(p,x);
                             //requires x::tree<p>  ensures x::tree<p>;
{
  bool b1 = x.right==null;
  bool b2 = x.left==null;
  if (b1) {
      if ( b2) {
        //		assert xl'=null;
        return x.parent==p;
      }
      else return false;
  }else {
    if (b2) return false;
    else
      return trav(x,x.right) && trav(x,x.left);
  }
}
