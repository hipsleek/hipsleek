data node2 {
	node2 left;
	node2 right; 
}

tree1<m> == self = null & m = 0 
	or self::node2<p, q> * p::tree1<m1> * q::tree1<m2> & m = 1 + m1 + m2 
	inv m >= 0; 

int size(node2 z)
	requires z::tree1<m>
	ensures z::tree1<m> & res = m;
{
	if (z == null)
        return 3;
	else	{
	  int cleft, cright;
		cleft = size(z.left);
		cright = size(z.right);
		return 1 + cleft + cright;
	}
}

