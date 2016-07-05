/* Complete Binary Tree */
/* Given Shape -> Infer Size + Height Property */

data node2 {
  int val;
  node2 left;
  node2 right;
}

/*
Complete binary tree:
- a binary tree in which every level, except possibly the deepest is completely filled
- at depth n, the height of the tree, all nodes are as far left as possible.
*/

complete<> == self = null
  or self::node2<_, l, r> * l::complete<> * r::complete<>;

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
  requires t::complete<>
  ensures t::complete<> & res>=0;
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
  requires t::complete<>
  ensures t::complete<> & res>=0;
{
  if (t != null)
    return maxim(height(t.left), height(t.right)) + 1;
  else 
    return 0;
}

int min_height(node2 t)
  requires t::complete<>
  ensures t::complete<> & res>=0;
{
  if (t != null)
    return minim(min_height(t.left), min_height(t.right)) + 1;
  else 
    return 0;
}

/* Insert an element into a complete binary tree */
void insert(ref node2 t, int v)
  requires t::complete<> 
  ensures t'::complete<>;
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
  requires t::complete<>
  ensures t::complete<> & (res = 0 | res = 1);
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
