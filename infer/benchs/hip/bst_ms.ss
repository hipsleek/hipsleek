/* trees & binary search trees */

/* representation of a node */
data node2 {
  int val;
  node2 left;
  node2 right;
}

/* view for trees with number of nodes and depth */
//size
bst0<m> == self = null & m = 0
	or self::node2<_, p, q> * p::bst0<m1> * q::bst0<m2> & m = 1 + m1 + m2
	inv m >= 0;

/* view for a doubly linked list with size */
dll<p, n> == self = null & n = 0
	or self::node2<_, p, q> * q::dll<self, n1> & n = n1+1
	inv n >= 0;

/* function to append 2 doubly linked lists */
relation APP(int a, int b, int c).
node2 append(node2 x, node2 y)
   infer[APP]
   requires x::dll<_, m> * y::dll<_, n>
     ensures res::dll<r, k> & APP(k,m,n);//m>=0 & k>=m & k=n+m
{
	node2 z;

	if (x == null)
		return y;
	else
	{
		z = append(x.right, y);
		x.right = z;
		if (z != null)
			z.left = x;

		return x;
	}
}

relation C(int a, int b, int c).
node2 appendC(node2 x, node2 y)
  infer [C]
  requires x::dll<q, m> * y::dll<p, n>
  ensures res::dll<_, k> & C(k,m,n);

{
	node2 tmp;

	if (x == null)
		return y;
	else
	{ 	

		tmp = x.right;
		tmp = appendC(tmp, y);

		if (tmp != null)
		{
			x.right = tmp; 
			tmp.left = x;
		}
		else {
			x.right = null;
		}

		return x; 
	}
}

/* function to count the number of nodes in a tree */
relation CNT(int a, int b, int c).
int count(node2 z)
  infer[CNT]
  requires z::bst0<n>
  ensures  z::bst0<n1> & CNT(res,n,n1);//res = n & n>=0 & n=n1;
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

/* function to transform a tree in a doubly linked list */
//fail to compute fixpoint if use append
//relation FLAT(int a, int b).
void flatten(node2 x)
  infer @post [x]
  requires x::bst0<m>
  ensures  x::dll<q, m1> ;//& q=null
{
	node2 tmp;
	if (x != null)
	{
		flatten(x.left);
		flatten(x.right);
		tmp = append(x.left, x.right);
		x.left = null;
		x.right = tmp;
		if (tmp != null)
			tmp.left = x;
	}
}

/* insert a node in a bst */
relation INS(int a, int b).
node2 insert(node2 x, int a)
  infer[INS]
  requires x::bst0<m>
  ensures res::bst0<m1> & res != null & INS(m,m1);//m>=0 & m+1=m1
{
	node2 tmp;
        node2 tmp_null = null;

	if (x == null)
      return new node2(a, null, null);
	else
	{
		if (a <= x.val)
		{
			tmp = x.left;
			x.left = insert(tmp, a);
		}
		else
		{ 
			//tmp = x.right;
			x.right = insert(x.right, a);
		}

		return x;
	} 
}

/* delete a node from a bst */
relation RMV_MIN(int a, int b).
int remove_min(ref node2 x)
  infer[RMV_MIN,x]
  requires x::bst0<n> //& x != null
  ensures x'::bst0<n1> & RMV_MIN(n,n1);//n1=n-1;//'
{
	int tmp, a;

	if (x.left == null)
	{
		tmp = x.val;
		x = x.right;

		return tmp;
	}
	else {
		int tmp;
		bind x to (_, xleft, _) in {
			tmp = remove_min(xleft);
        }

		return tmp;
	}
}

int remove_min1(ref node2 x)
  requires x::bst0<n> & x != null
  ensures x'::bst0<n-1>;//'

relation DEL(int a, int b).
void delete(ref node2 x, int a)
  infer[DEL]
  requires x::bst0<n1>
  ensures x'::bst0<n> & DEL(n,n1);//& n1<=n & h1<=h;//'
{
	int tmp;

	if (x != null)
	{
       bind x to (xval, xleft, xright) in
      {
        if (xval == a)
          {
            if (xright == null) {
              //assert true;
              x = xleft;
            }
            else
              {
                tmp = remove_min1(xright);
                //assert true;
                xval = tmp;
              }
          }
        else
          {
            if (xval < a)
              delete(xright, a);
            else
              delete(xleft, a);
          }
      }
	}
}

/*
Traversals
- depth-first traversal
- breadth-first traversal

There are three different types of depth-first traversals, :
- PreOrder traversal - visit the parent first and then left and right children;
- InOrder traversal - visit the left child, then the parent and the right child;
- PostOrder traversal - visit left child, then the right child and then the parent;
*/
//DFS
relation TRAV(int a, int b).
void traverse(node2 x)
  infer[TRAV]
  requires x::bst0<n>//0<=h & h<=n
  ensures x::bst0<n1>& TRAV(n,n1);//'h1>=0 & n1>=h1 & h1=h & n1=n
{
  if (x != null){
    bind x to (xval, xleft, xright) in
    {
      //process xval
      traverse(xleft);
      traverse(xright);
    }
  }
}

//Searching
relation SEA(int a, int b).
bool search(node2 x, int a)
  infer[SEA]
  requires x::bst0<n>
  ensures x::bst0<n1> & (res | !res) & SEA(n,n1);//'n>=0 & h>=0 & n=n1 & h=h1
{
	int tmp;

	if (x != null)
	{
      bind x to (xval, xleft, xright) in
      {
        if (xval == a)
          return true;
        else {
            if (xval < a)
              search(xright, a);
            else
              search(xleft, a);
        }
      }
      return false;
	}
    else return false;
}

/*************************************************************/

