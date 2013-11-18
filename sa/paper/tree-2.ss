// simpler tll working example

data node{
  node parent;
  node left;
  node right;
}

// predicate for a non-empty tree with chained leaf list

// predicate for a non-empty tree
 tree<p> == self::node<p,_,null>
	or self::node<p,l,r> * l::tree<self> * r::tree<self>
	inv self!=null;

// initializes the linked list fields

HeapPred H(node a, node@NI b).
HeapPred G(node a, node@NI b).

void trav ( node p,  node x)
 infer [H,G] requires H(x,p) ensures G(x,p);
// requires x::tree<p> ensures x::tree<p>;

{
  node xp = x.parent;
  node xl = x.left;
  node xr = x.right;
  assert p=xp' assume p=xp';
  if (x.right == null)
    {    return ;
    }
  else
    {
      trav(x,xr);
      trav(x,xl);
    }
  return;
}
