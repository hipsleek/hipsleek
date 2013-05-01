/* Complete Binary Tree */
/* Given Shape + Size + Height -> Infer Bag Property */

data node2 {
  int val;
  node2 left;
  node2 right;
}

/*
Complete binary tree:
- a binary tree in which every level, 
  except possibly the deepest is completely filled
- at depth n, the height of the tree, 
  all nodes are as far left as possible.

The property that we used:
- n is the size
- h is the height
- nmin is the "minimum height"
  - is the length of the shortest path to a leaf 
    (the minimum between the heights for the two children)
  - we use it to make the insertion easier 
    (because in the insertion there are points 
    where we need to know if a subtree is perfect or not)
*/

completeNH<n,h,nmin> == 
     self = null & n = 0 & h = 0 & nmin = 0
  or self::node2<_,l,r> * l::completeNH<nl1,h-1,nmin1> 
     * r::completeNH<nr1,h-2,nmin2> 
     & nmin = min(nmin1,nmin2)+1 & n=nl1+nr1+1
  or self::node2<_,l,r> * l::completeNH<nl2,h-1,nmin1> 
     * r::completeNH<nr2,h-1,nmin2> 
     & nmin = min(nmin1,nmin2)+1 & n=nl2+nr2+1;

/************************************************************/

int maxim(int a, int b)
  requires true
  ensures (a < b & res = b) | (a >= b & res = a);
{
  if(a >= b)
    return a;
  else
    return b;
}

int minim(int a, int b)
  requires true
  ensures (a < b & res = a) | (a >= b & res = b);
{
  if(a >= b)
    return b;
  else
    return a;
}

/* Count the number of nodes in a tree */
int count(node2 t)
  requires t::completeNH<n, h, nmin>
  ensures t::completeNH<n, h, nmin> & res=n;
{
  int cleft, cright;

  if (t == null)
    return 0;
  else
  {
    cleft = count(t.left);
    cright = count(t.right);
    return (1 + cleft + cright);
  }
}

int height(node2 t)
  requires t::completeNH<n, h, nmin>
  ensures t::completeNH<n, h, nmin> & res=h;
{
  if (t != null)
    return maxim(height(t.left), height(t.right)) + 1;
  else 
    return 0;
}

int min_height(node2 t)
  requires t::completeNH<n, h, nmin>
  ensures t::completeNH<n, h, nmin> & res = nmin;
{
  if (t != null)
    return minim(min_height(t.left), min_height(t.right)) + 1;
  else 
    return 0;
}

/* Insert an element into a complete binary tree */
void insert(ref node2 t, int v)
  requires t::completeNH<n,h1,nmin> & nmin < h1
  ensures t'::completeNH<n+1,h2,nmin1> & (nmin1=nmin | nmin1=nmin+1) & h1=h2 ;
  requires t::completeNH<n,h1,nmin> & nmin = h1
  ensures t'::completeNH<n+1,h2,nmin1> & (nmin1=nmin | nmin1=nmin+1) & h2=h1+1;
{
  node2 aux;

  if(t == null) {
    t = new node2(v, null, null);
    return;
  }
  else 
  {
    if(min_height(t.left) < height(t.left)) 
    {    // there is still space in the left subtree
      aux = t.left;
      insert(aux, v);
      t.left = aux;
      return;
    }
    else {
      if(min_height(t.right) < height(t.right)) 
      {  // there is still space in the right subtree
        aux = t.right;
        insert(aux, v);
        t.right = aux;
        return;
      }
      else {
        node2 tmp = t.right;
        if(height(t.left) == height(t.right)) 
        { // tree is full - we must start another level
          aux = t.left;
          insert(aux, v);
          t.left = aux;
          return;
        }
        else {
          aux = t.right;
          insert(aux, v);
          t.right = aux;
          return;
        }
      }
    }
  }
}

int is_perfect(node2 t)
  requires t::completeNH<n,h,nmin>
  ensures t::completeNH<m,h,nmin> & (nmin != h | res = 1) & (nmin = h | res = 0) & m=n;
{
  if(t == null)
    return 1;
  else {
    if(height(t.left) != height(t.right))
      return 0;
    else {
      if(is_perfect(t.left) == 1)
        return is_perfect(t.right);
      else
        return 0;
    }
  }
}
