data node2 {
	node2 left;
	node2 right; 
}

/* view for trees with number of nodes */
tree1<m> == self = null & m = 0 
	or self::node2<p, q> * p::tree1<m1> * q::tree1<m2> & m = 1 + max(m1,m2)
	inv m >= 0; 

/* function to count the number of nodes in a tree */
int height(node2 z)
	requires z::tree1<m>
	ensures z::tree1<m> & res = m & res >= 0;
{
  if (z == null)
		return 0;
	else{
		int cleft = height(z.left);
		int cright = height(z.right);
		if (cleft > cright) return 3 + cleft;
    else return 1 + cright;
	}
}

