/* trees & binary search trees */

/* representation of a node */
data node2 {
	int val;
	node2 left;
	node2 right; 
}
/* binary search trees */
/* view for binary search trees */
bst2 <n,h, sm, lg> == self = null & sm <= lg & n = 0 & h = 0
  or (exists pl,qs: self::node2<v, p, q> * p::bst2<n1,h1,sm, pl> *
      q::bst2<n2,h2,qs, lg> & pl <= v & qs >= v & n=n1+n2+1 & h=1+max(h1,h2))
	inv h >= 0 & n >= 0 & sm <= lg;


/* view for a doubly linked list with size */
dll<p, n> == self = null & n = 0
	or self::node2<_, p, q> * q::dll<self, n1> & n = n1+1
	inv n >= 0;

/* function to append 2 doubly linked lists */
node2 append(node2 x, node2 y)
     requires x::dll<_, m> * y::dll<_, n>
     ensures res::dll<r, m+n>;
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
int count(node2 z)
  requires z::bst2<n,h,sm, lg>@I
  ensures res =n;
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

void flatten(node2 x)
  requires x::bst2<n,h,sm, lg>
  ensures (exists q : x::dll<q, n> & q=null);
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
relation C(int x, int y, int z, int a, int b).
node2 insert(node2 x, int a)
  infer [C]
  requires x::bst2<n,h,sm, lg>
  ensures res::bst2<n+1,h1,mi, ma> & h1>=h
  & res != null & C(mi,sm,lg,ma, a);//mi = min(sm, a) & ma = max(lg, a);a>=mi & ma>=a 
{
	node2 tmp;
    node2 tmp_null = null;

	if (x == null){
      assume mi=min(sm,a);
      assume ma=max(lg,a);
      return new node2(a, null, null);
    }
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
relation RMVM(int x, int y, int z).
int remove_min(ref node2 x)
  infer[RMVM]
  requires x::bst2<n,h,s, b> & x != null
  ensures x'::bst2<n-1,h1,s1, b> & h1<=h & RMVM(s,res,s1);//s <= res <= s1;//'
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
  requires x::bst2<n,h,s, b> & x != null
  ensures x'::bst2<n-1,h1,s1, b> & h1<=h & s <= res <= s1;//'

relation DEL(int x, int y, int z, int a).
void delete(ref node2 x, int a)
  infer[DEL]
  requires x::bst2<n,h,sm, lg>
  ensures x'::bst2<n1,h1,s, l> & n1<=n & h1<=h & DEL(sm,s,l,lg);//sm <= s & l <= lg;//'DEL(sm,s,l,lg,a)
{
	int tmp;

	if (x != null)
	{
      bind x to (xval, xleft, xright) in
		{
          if (xval == a)
			{
              if (xright == null) {
                assert true;
                x = xleft;
              }
              else
				{
                  tmp = remove_min1(xright);
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
  else {
    assume sm<=s;
    assume l<=lg;
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
  requires x::bst2<n, h,sm, lg>
  ensures x::bst2<n, h,sm, lg>;//'
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
relation SEARCH(int a, int b, int c).
bool search(node2 x, int a)
  infer[SEARCH]
  requires x::bst2<n, h,sm, lg>
  ensures x::bst2<n, h,sm, lg> & !res or x::bst2<n,h,sm,lg> & res & SEARCH(sm,a,lg);//(res & sm<=a<=lg | !res);//'sm<=a<=lg SEA(sm,a,lg)
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
  else {
    return false;
  }
}

/*************************************************************/

