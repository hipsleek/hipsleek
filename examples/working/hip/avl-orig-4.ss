data node {
	int ele;
	int height;
	node left;
	node right;
}

// m: number of elements, n: height
// bal: 0: left is higher, 1: balanced, 2: right is higher

 avl<n, h> == 
      self = null & h = 0 & n = 0
   or self::node<_, h, p, q> * p::avl<n1, h1> * q::avl<n2, h2>
		& n = 1+n1+n2 & h=1+max(h1, h2) & -1 <= h1-h2 <=1 
 inv h >= 0 & n >= 0;


 avl2<n, h> == 
      self = null & h = 0 & n = 0
   or self::node<_, h, p, q> * p::avl2<n1, h1> * q::avl2<n2, h2>
		& n = 1+n1+n2 & h=1+max(h1, h2) & -1 <= h1-h2 <=1 
 inv h >= 0 & n >= 0 & n>=h;

/* function to return the height of an avl tree */
int height(node x)
	requires x::avl<n, h>
	ensures x::avl<n, h> & res = h;
{
  dprint;
	if (x == null)
		return 0;
	else
		return x.height;
}

/* function to return the height of an avl tree */
int height2(node x)
	requires x::avl2<n, h>
	ensures x::avl2<n, h> & res = h;
{
  dprint;
	if (x == null)
		return 0;
	else
		return x.height;
}


