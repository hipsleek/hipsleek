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

int get_max(int a , int b)
	requires true 
	ensures res = max(a, b);
{
	if (a >= b)
		return a;
	else
		return b;
}

/* double left rotation */
node rotate_double_left(node a, node b, node c, node d)
	requires a::avl<am, an> * b::avl<bm, bn> * c::avl<cm, cn> * d::avl<dm, an> & an = max(bn, cn) 
	         & -1 <= bn - cn <= 1
	ensures res::avl<3 + am + bm + cm + dm, an + 2>;

{
	int h1;
	h1 = get_max(height(a), height(b));
	node tmp1;
	tmp1 = new node(h1+1, a, b);

  int h2;
	h2 = get_max(height(c), height(d));
  node tmp2;
	tmp2 = new node(h2 + 1, c.left, d);

  int h3;
	h3 = get_max(h1, h2) + 1;
  return new node(h3+1, tmp1, tmp2);
}
