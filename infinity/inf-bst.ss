/* binary search trees */

data node2 {
	int val;
	node2 left;
	node2 right; 
}

/* view for binary search trees */
bst <sm, lg> == self = null & sm =\inf & lg=-\inf
	or self::node2<v, p, q> * p::bst<sm1, lg1> * q::bst<sm2, lg2> 
  & lg1<=v & v<=sm2 & sm=min(sm1,v) & lg=max(lg2,v)
  //inv true;
  // inv self=null | self!=null & sm<=lg;
  inv self=null & sm=\inf & lg=-\inf 
           | self!=null & sm<=lg; // why fail for insert?

/* insert a node in a bst */
node2 insert(node2 x, int a)
	requires x::bst<sm, lg> 
	ensures res::bst<mi, ma> & mi = min(sm, a) & ma = max(lg, a);
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
			//tmp = x.right;
			x.right = insert(x.right, a);
		}

		return x;
	} 
}

/* delete a node from a bst */

/*
void delete(ref node2 x, int a)

	requires x::bst<sm, lg> 
	ensures x'::bst<s, l> & sm <= s & l <= lg;

{
	int tmp; 

	if (x != null)
	{
		bind x to (xval, xleft, xright) in 
		{
			if (xval == a) 
			{
				if (xright == null) {
                    assert true;
					x = xleft; 
				}
				else
				{
					tmp = remove_min(xright);
					xval = tmp;
				}
			}
			else
			{
				if (xval < a)
					delete(xright, a);
				else
					delete(xleft, a);
			}
		}
	}
}
*/
int remove_min(ref node2 x)
	requires x::bst<s, b> & x != null 
	ensures x'::bst<s1,b2> & res=s ; //'
{
	int tmp, a; 

	if (x.left == null)
	{
		tmp = x.val;
		x = x.right;

		return tmp; 
	}
	else {
      //assume false;
		int tmp;
		bind x to (_, xleft, _) in { 
			tmp = remove_min(xleft);
		}

		return tmp;
	}
}

