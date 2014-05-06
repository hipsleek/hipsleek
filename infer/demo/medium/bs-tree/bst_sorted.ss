/* Binary Search Trees */
/* Given Shape + Size + Height -> Infer Sortedness Property */

data node2 {
  int val;
  node2 left;
  node2 right;
}

bstNH<n, h> == self = null & n = 0 & h = 0
  or self::node2<_, p, q> * p::bstNH<n1, h1> * q::bstNH<n2, h2> 
     & n = 1 + n1 + n2 & h = 1 + max(h1, h2);

dllN<p, n> == self = null & n = 0
  or self::node2<_, p, q> * q::dllN<self, n1> & n = n1+1;

/******************************************/

/* Append a doubly linked list by another one */
node2 append(node2 x, node2 y)
  requires x::dllN<_,m> * y::dllN<_,n>
  ensures res::dllN<_,z> & z=m+n;
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

/* Count the number of nodes in a tree */
int count(node2 z)
  requires z::bstNH<n, h>
  ensures  z::bstNH<n, h> & res = n;
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

/* Transform a tree into a doubly linked list */
void flatten(node2 x)
  requires x::bstNH<m, h>
  ensures  x::dllN<q, m1> & q=null & m1=m;
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

/* Insert an element into a bst */
node2 insert(node2 x, int a)
  requires x::bstNH<m, n>
  ensures res::bstNH<m+1, n1> & n1>=n & res != null;
{
  node2 tmp;
  node2 tmp_null = null;

  if (x == null){
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
      x.right = insert(x.right, a);
    }

    return x;
  } 
}

/* Delete a node from a bst */
int remove_min(ref node2 x)
  requires x::bstNH<sn, n> & x != null
  ensures x'::bstNH<sn-1, n1> & n1<=n & n1+1>=n;
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
    bind x to (_, xleft, _) in 
    {
      tmp = remove_min(xleft);
    }

    return tmp;
  }
}

void delete(ref node2 x, int a)
  requires x::bstNH<h, n>
  ensures x'::bstNH<h1, n1> & n1<=n & h1<=h;
{
  int tmp;

  if (x != null)
  {
    bind x to (xval, xleft, xright) in
    {
      if (xval == a)
      {
        if (xright == null) {
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

/* One kind of traversal of bst */
void traverse(node2 x)
  requires x::bstNH<n, h>
  ensures x::bstNH<n, h>;
{
  if (x != null){
    bind x to (xval, xleft, xright) in
    {
      traverse(xleft);
      traverse(xright);
    }
  }
}

// Search for an element
bool search(node2 x, int a)
  requires x::bstNH<n, h>
  ensures x::bstNH<n, h> & (res | !res) & n>=0 & h>=0;
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
  else 
    return false;
}

