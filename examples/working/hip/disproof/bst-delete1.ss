data node2 {
	int val;
	node2 left;
	node2 right; 
}


bst <sm, lg> == self = null & sm <= lg 
	or (exists pl,qs: self::node2<v, p, q> * p::bst<sm, pl> * q::bst<qs, lg> & pl <= v & qs >= v)
	inv sm <= lg;

int remove_min(node2@R x)
	requires x::bst<s, b> & x != null 
	ensures x'::bst<s1, b> & s <= res <= s1;
{
	int tmp, a; 

	if (x.left == null)
	{
		tmp = x.val;
		x = x.left;

		return tmp; 
	}
	else {
		int tmp;
		bind x to (_, xleft, xright) in { 
			tmp = remove_min(xleft);
		}

		return tmp;
	}
}

void delete(node2@R x, int a)
	requires x::bst<sm, lg> 
	ensures x'::bst<s, l> & sm <= s & l <= lg;

{
	int tmp; 

	if (x != null){
		bind x to (xval, xleft, xright) in 
		{
			if (xval == a) {
				if (xright == null) {
					x = xleft; 
				}	else	{
					tmp = remove_min(xright);
					xval = tmp;
				}
			}	else
			{
				if (xval < a)
					delete(xright, a);
				else
					delete(xleft, a);
			}
		}
	}
}
