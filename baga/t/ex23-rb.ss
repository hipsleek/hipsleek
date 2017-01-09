/* red black trees */

data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
}

/* view for red-black trees */
rb<n, cl, bh> == self = null & n=0 & bh = 1 & cl = 0 
	or self::node<v, 1, l, r> * l::rb<nl, 0, bhl> * r::rb<nr, 0, bhr> & cl = 1 & n = 1 + nl + nr & bhl = bh & bhr = bh
	or self::node<v, 0, l, r> * l::rb<nl, _, bhl> * r::rb<nr, _, bhr> & cl = 0 & n = 1 + nl + nr & bhl = bhr & bh = 1 + bhl
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1;

/*
--inv-baga

 inv: 0<=cl & cl<=n & cl<=self & cl<=1 & 1<=bh
  baga over inv:
   [([], self=null & n=0 & bh=1 & cl=0),([self], 1<=n & 1<=bh & cl=1),([self], 1<=n & 2<=bh & cl=0)]
  baga over inv (unfolded):
   [([], self=null & n=0 & bh=1 & cl=0),([self], 1<=n & 1<=bh & cl=1),([self], 1<=n & 2<=bh & cl=0)]


 inv: 0<=n  & 0<=cl            & cl<=1 & 1<=bh
  baga over inv: [([], 0<=n & 1<=bh & 0<=cl & cl<=1)]
  baga over inv (unfolded):
   [([self], ((0-bh)+2)<=cl & 0<=cl & cl<=1 & 1<=n),([], self=null & n=0 & bh=1 & cl=0)]
*/
/* rotation case 3 */
/*
node rotate_case_3(node a, node b, node c)

	requires a::rb<na, 1, bha> * b::rb<nb, 0, bha> * c::rb<nc, 0, bha> 
	ensures res::rb<na + nb + nc + 2, 0, bha + 1>;

{
	node tmp;

	tmp = new node(0, 1, b, c);
	
	return new node(0, 0, a, tmp);
}
*/




