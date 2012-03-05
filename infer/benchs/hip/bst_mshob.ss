/* trees & binary search trees */

/* representation of a node */
data node2 {
	int val;
	node2 left;
	node2 right; 
}
/* binary search trees */
/* view for binary search trees */
//size, height, sortedness, bag
bst3 <n,h, sm, lg,S> == self = null & sm <= lg & n = 0 & h = 0 & S={}
  or (exists pl,qs: self::node2<v, p, q> * p::bst3<n1,h1,sm, pl,S1> *
      q::bst3<n2,h2,qs, lg,S2> & pl <= v & qs >= v & n=n1+n2+1 & h=1+max(h1,h2)
      & S=union(S1,S2,{v}))
	inv h >= 0 & n >= 0 & sm <= lg;

/* view for a doubly linked list with size */
dll<p, n,S> == self = null & n = 0 & S={}
  or self::node2<v, p, q> * q::dll<self, n1,S1> & n = n1+1 & S=union(S1,{v})
	inv n >= 0;

/* function to append 2 doubly linked lists */
//wo --eps
relation APP(bag a, bag b, bag c).
node2 append(node2 x, node2 y)
  infer[APP]
  requires x::dll<_, m,S1> * y::dll<_, n,S2>
  ensures res::dll<r, m+n,S> & APP(S,S1,S2);//S=union(S1,S2);
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

node2 append1(node2 x, node2 y)
  requires x::dll<_, m,S1> * y::dll<_, n,S2>
  ensures res::dll<r, m+n,S> & S=union(S1,S2);

relation C(bag x, bag y, bag z).
node2 appendC(node2 x, node2 y)
  infer [C]
  requires x::dll<q, m,S1> * y::dll<p, n,S2>
  ensures res::dll<_, m+n,S> & C(S,S1,S2);

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
int count(node2 z)
  requires z::bst3<n,h,sm, lg,S>@I
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

relation FLAT(bag x, bag y).
void flatten(node2 x)
//  infer[FLAT]
  requires x::bst3<n,h,sm, lg,S1>
  ensures x::dll<q, n,S2> & S1=S2;//S1=S2;FLAT(S1,S2)
{
  node2 tmp;
  if (x != null)
	{
      flatten(x.left);
      flatten(x.right);
      tmp = append1(x.left, x.right);
      x.left = null;
      x.right = tmp;
      if (tmp != null)
        tmp.left = x;
	}
}

/* insert a node in a bst */
//mona fails
node2 insert(node2 x, int a)
  requires x::bst3<n,h,sm, lg,S1>
  ensures res::bst3<n+1,h1,mi, ma,S2> & h1>=h
  & res != null & mi = min(sm, a) & ma = max(lg, a) & S2=union(S1,{a});
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
//mona fails while inferring
relation RMVM(bag x, bag y).
int remove_min(ref node2 x)
  infer[RMVM]
  requires x::bst3<n,h,s, b,S1> & x != null
  ensures x'::bst3<n-1,h1,s1, b,S2> & h1<=h & s <= res <= s1 & RMVM(S1,S2);//S2 subset S1;//'RMVM(S1,S2);//
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

relation DEL(bag x, bag y).
void delete(ref node2 x, int a)
//infer[DEL]
  requires x::bst3<n,h,sm, lg,S1>
  ensures x'::bst3<n1,h1,s, l,S2> & n1<=n & h1<=h & sm <= s & l <= lg;//DEL(S1,S2);
   // & S2 subset S1;//'
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
                  tmp = remove_min(xright);
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
relation TRA(bag x, bag y).
//fail to compute the fixpoint
void traverse(node2 x)
//infer[TRA]
  requires x::bst3<n, h,sm, lg,S1>
  ensures x::bst3<n, h,sm, lg,S1> ;//& TRA(S1,S2);//'
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
relation SEA(bag x, int y).
//fail
bool search(node2 x, int a)
//infer[SEA]
  requires x::bst3<n, h,sm, lg,S>
  ensures x::bst3<n, h,sm, lg,S> & (res & sm<=a<=lg & a in S | !res );//' a in S
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

