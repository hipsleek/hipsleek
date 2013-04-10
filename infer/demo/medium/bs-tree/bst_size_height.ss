/* Binary Search Trees */
/* Given Shape -> Infer Size + Height Property */

data node2 {
  int val;
  node2 left;
  node2 right;
}

bst<> == self = null
  or self::node2<_, p, q> * p::bst<> * q::bst<>;

dll<p> == self = null
  or self::node2<_, p, q> * q::dll<self>;

/******************************************/

/* Append a doubly linked list by another one */
node2 append(node2 x, node2 y)
  requires x::dll<_> * y::dll<_>
  ensures res::dll<_>;
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
  requires z::bst<>
  ensures z::bst<> & res>=0;
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
  requires x::bst<>
  ensures  x::dll<_> & q=null;
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
  requires x::bst<>
  ensures res::bst<> & res != null;
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
  requires x::bst<> & x != null
  ensures x'::bst<>;
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
  requires x::bst<>
  ensures x'::bst<>;
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
  requires x::bst<>
  ensures x::bst<>;
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
  requires x::bst<>
  ensures x::bst<> & (res | !res);
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

