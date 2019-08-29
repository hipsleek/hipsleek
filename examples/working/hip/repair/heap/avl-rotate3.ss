data node {
	int height;
	node left;
	node right;
}

avl<size, height> == self = null & size = 0 & height = 0 
	or self::node<height, p, q> * p::avl<size1, height1> * q::avl<size2, height2>
  & size = 1+size1+size2
  & height2<=height1+1 & height1<=height2+1 & height = max(height1, height2) + 1 
	& size > 0 & height > 0;

int height(node x)
	requires x::avl<m, n>
	ensures x::avl<m, n> & res = n;	

{
	if (x == null)
		return 0;
	else
		return x.height;        
}

node rotate_left(node l, node rl, node rr)
	requires l::avl<lm, ln> * rl::avl<rlm, ln> * rr::avl<rrm, ln+1>
	ensures res::avl<2+lm+rlm+rrm, 2+ln>;	

{
	int h;	
	h = height(l) + 3;
  // h = height(l) + 1;
	node tmp;
	tmp = new node(h, l, rl);
  node tmp2;
  tmp2 = new node(h+1, tmp, rr);
  return tmp2;
}