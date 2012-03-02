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

int remove_min(ref node2 x)
        infer [x,A]
	requires x::bst<s, b> //& x != null 
	ensures x'::bst<s1, b> & A(s,res,s1); //s <= res <= s1;

{
	int tmp, a; 

	if (x.left == null)
	{
		tmp = x.val;
		x = x.right;

		return tmp; 
	}
	else {
		int tmp;
		bind x to (_, xleft, _) in { 
			tmp = remove_min(xleft);
		}

		return tmp;
	}
}
