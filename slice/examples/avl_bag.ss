data node {
	int val;
	int height;
	node left;
	node right;
}
/*
avl<n, h, s, B> ==
	self = null & h = 0 & n = 0 & s = 0 & B = {} or
	self::node<v, p, q> * p::avl<n1, h1, s1, B1> * q::avl<n2, h2, s2, B2>
	    & v >= 0
		& n = 1 + n1 + n2
		& h = 1 + max(h1, h2) & -1 <= h1 - h2 <= 1
		& s = v + s1 + s2
		& B = union({v}, B1, B2)
	inv h >= 0 & n >= 0 & n >= h & s >= 0;
*/

avl<n, h, B> ==
	self = null & h = 0 & n = 0 & B = {} or
	self::node<v, h, p, q> * p::avl<n1, h1, B1> * q::avl<n2, h2, B2>
	    & v >= 0
		& n = 1 + n1 + n2
		& h = 1 + max(h1, h2) & -1 <= h1 - h2 <= 1
		& B = union({v}, B1, B2)
	inv h >= 0 & n >= 0 & n >= h;

/* function to return the height of an avl tree */
int height(node x)
  requires x::avl<n, h, B>
  ensures x::avl<n, h, B> & res = h;
{
  int tmpi;
  if (x == null)
    return 0;
  else
    return x.height;
}
