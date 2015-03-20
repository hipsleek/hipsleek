data node2 {
	int val;
	node2 left;
	node2 right; 
}

/* view for trees with number of nodes */
tree<m> == self = null & m = 0 
	or self::node2<_, p, q> * p::tree<m1> * q::tree<m2> & m = 1 + m1 + m2 
	inv m >= 0 ;

inftree<m1,m2> == self = null & m1 = 0 & m2 = 0
	or self::node2<_, p, q> * p::inftree<m1-1,m2> * q::inftree<m1-1,m2>
	or self::node2<_, p, q> * p::inftree<m1,m2-1> * q::inftree<m1,m2-1>
	or self::node2<_, p, q> * p::inftree<m1-1,m2> * q::inftree<m1-1,m2>
	or self::node2<_, p, q> * p::inftree<m1,m2-1> * q::inftree<m1,m2-1>
	inv m1 >= 0 & m2 >= 0;

/* function to count the number of nodes in a tree */
int count(node2 z)

//	requires z::tree<\inf>
//	ensures z::tree<\inf> & res = \inf & res >= 0;

	requires z::inftree<\inf,\inf>
	ensures z::inftree<\inf,\inf> & res = \inf & res >= 0;

{
	int cleft, cright;

	if (z == null)
		return 0;
	else
	{
		cleft = count(z.left);
		cright = count(z.right);
		return (1 + cleft + cright);
	}
}

