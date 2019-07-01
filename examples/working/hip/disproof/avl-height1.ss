data node {
	int val;
	int height;
	node left;
	node right;
}

avl<size, height> == self = null & size = 0 & height = 0 
	or self::node<_, height, p, q> * p::avl<size1, height1> * q::avl<size2, height2> & size = 1+size1+size2 & 
        height2<=height1+1 & height1<=height2+1 & height = max(height1, height2) + 1 
	inv size >= 0 & height >= 0;

int height(node x)
	requires x::avl<m, n>
	ensures x::avl<m, n> & res = n;	
{
	if (x == null)
		return 3;
	else
		return 3 + x.height;        
}
