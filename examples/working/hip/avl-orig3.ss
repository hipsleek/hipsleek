data node {
	int ele;
	int height;
	node left;
	node right;
}

// m: number of elements, n: height
// bal: 0: left is higher, 1: balanced, 2: right is higher

avl<m, n, bal> == self = null & m = 0 & n = 0 & bal=1
	or self::node<_, n, p, q> * p::avl<m1, n1, _> * q::avl<m2, n2, _>
		& m = 1+m1+m2 & n = max(n1, n2) + 1 
		// -1 <= n1-n2 <=1 
		& n2+bal=n1+1 & n2<=n1+1 & n1 <= 1+n2
	inv m >= 0 & n >= 0 & 0<=bal<=2;


 avl2<n, h> == 
      self = null & h = 0 & n = 0
   or self::node<_, h, p, q> * p::avl2<n1, h1> * q::avl2<n2, h2>
		& n = 1+n1+n2 & h=1+max(h1, h2) & -1 <= h1-h2 <=1 
 inv h >= 0 & n >= 0 & n>=h;

/* function to return the height of an avl tree */
int height(node x)
	requires x::avl<m, n, b>
	ensures x::avl<m, n, b> & res = n;

{
  dprint;
	if (x == null)
		return 0;
	else
		return x.height;
}

int get_max(int a, int b) 
	requires true ensures res=a & a>=b or res=b & b>a;
{
	if (a>=b) return a;
	else return b;
}

node insert(node t, int x) 
  requires t::avl<tm, tn, b>
  ensures res::avl<tm+1, resn, resb> & t!=null & tm>0 & tn>0 & (tn=resn | resn=tn+1 & resb!=1)
		or res::avl<1,1,1> & tn=0 & tm=0 & t=null;
// --eps needs --esi
{
	node tmp = null;
	if (t==null) 
		return new node(x, 1, tmp, tmp);
	else if (x < t.ele) {		

