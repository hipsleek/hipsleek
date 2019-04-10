data node2 {
	int val;
	node2 left;
	node2 right; 
}

bst <m, sm, lg> == self = null & sm <= lg & m = 0
	or (exists pl,qs: self::node2<v, p, q> * p::bst<m1, sm, pl> * q::bst<m2, qs,
	lg> & pl <= v & qs >= v &  m = 1 + max(m1, m2))
	inv sm <= lg;

/* insert a node in a bst */
node2 insert(node2 x, int a)
	requires x::bst<sm, lg> 
	ensures res::bst<mi, ma> & res != null & mi = min(sm, a) & ma = max(lg, a);
	
{
	node2 tmp;
  node2 tmp_null = null;

	if (x == null)
		return new node2(a, null, null);
	else
	{
		if (a <= x.val)
		{
			tmp = x.left;
			x.left = insert(tmp, a);
		}
		else
		{ 
			x.right = insert(x.right, a);
		}

		return x;
	} 
}

int size(node2 x)
    requires x::bst<size, sm, lg>
    ensures x::bst<size, sm, lg> & res = size;
{
  if (x == null) return 0;
  else {
       int cleft, cright;
       cleft = size(x.left);
       cright = size(x.right);
       if (cleft > cright) return 1 + cleft;
       else return 1 + cright;
  }
}
