/* binary search trees */

data node2 {
	int val;
	node2 left;
	node2 right; 
}


/* view for binary search trees */
bst <sm, lg> == self = null & sm <= lg 
	or (exists pl,qs: self::node2<v, p, q> * p::bst<sm, pl> * q::bst<qs, lg> & pl <= v & qs >= v)
	inv sm <= lg;


relation A(int x, int y, int z).
relation B(int x, int y).
relation C(int x, int y, int z, int a, int b).

/* insert a node in a bst */
node2 insert(node2 x, int a)
  infer  [A]
  requires x::bst<sm, lg> 
  ensures res::bst<mi, ma> & res!=null & A(mi, sm, a) & ma = max(lg, a);  
	
{
  node2 tmp;
	if (x == null){
    // TODO:
    assume mi=min(sm,a);
    assume ma=max(lg,a);
    return new node2(a, null, null);
/*    node2 n = new node2(a, null, null);
    dprint;
		return n;*/
  }
	else
	{
    //assume false;
		if (a <= x.val)
		{
			tmp = x.left;
			x.left = insert(tmp, a);
		}
		else
		{ 
			//tmp = x.right;
			x.right = insert(x.right, a);
		}
    //dprint;
		return x;
	} 
}

