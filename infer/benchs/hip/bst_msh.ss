/* trees & binary search trees */

/* representation of a node */
data node2 {
  int val;
  node2 left;
  node2 right;
}

/* view for trees with number of nodes and depth */
//size, height
bst1<m, n> == self = null & m = 0 & n = 0
	or self::node2<_, p, q> * p::bst1<m1, n1> * q::bst1<m2, n2> & m = 1 + m1 + m2 & n = 1 + max(n1, n2)
	inv m >= 0 & n >= 0;

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

/* function to count the number of nodes in a tree */
relation CNT(int a, int b, int c).
int count(node2 z)
  infer[CNT]
  requires z::bst1<n, h>
  ensures  z::bst1<n, h> & CNT(res,n,n1);//res = n & n>=0 & n=n1;
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
//fail to compute fixpoint
relation FLAT(int a, int b).
void flatten(node2 x)
  infer[FLAT]
  requires x::bst1<m, n>
  ensures  x::dll<q, m> & q=null & FLAT(n,m);//& q=null
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

/* binary search trees */

/* view for binary search trees */
bst <sm, lg> == self = null & sm <= lg 
	or (exists pl,qs: self::node2<v, p, q> * p::bst<sm, pl> * q::bst<qs, lg> & pl <= v & qs >= v)
	inv sm <= lg;


/* insert a node in a bst */
relation INS(int a, int b).
node2 insert(node2 x, int a)
  infer[INS]
  requires x::bst1<m, h>
  ensures res::bst1<m+1, h1> & res != null & INS(h,h1);
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

int remove_min(ref node2 x)
  infer[x]
  requires x::bst1<n, h> & x != null
  ensures x'::bst1<n-1, h1> & h1<=h;//'
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

void delete(ref node2 x, int a)
  requires x::bst1<n, h>
  ensures x'::bst1<n1, h1> & n1<=n & h1<=h;//'
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
                tmp = remove_min(xright);
                assert true;
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
void traverse(node2 x)
  requires x::bst1<n, h>
  ensures x::bst1<n, h>;//'
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
bool search(node2 x, int a)
  requires x::bst1<n, h>
  ensures x::bst1<n, h> & (res | !res);//'
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

