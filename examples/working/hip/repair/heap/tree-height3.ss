data node2 {
	int val;
	node2 left;
	node2 right; 
}

/* view for trees with number of nodes */
tree1<m> == self = null & m = 0 
	or self::node2<_, p, q> * p::tree1<m1> * q::tree1<m2> & m = 1 + max(m1,m2)
	inv m >= 0; 

/* function to count the number of nodes in a tree */
int height(node2 z)
	requires z::tree1<m>
	ensures z::tree1<m> & res = m;
{
	if (z == null)
		return 0;
	else
	{
    int cleft, cright;
		cleft = height(z.left);
		cright = height(z.right.left);
		if (cleft > cright) return 1 + cleft;
    else return 1 + cright;
	}
}
