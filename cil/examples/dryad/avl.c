#define MAX(A, B) ((A) > (B) ? (A) : (B)) 

struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};

/*@
avl<size, height, S> == self = null & size = 0 & height = 0 & S = {}
  or self::node^<v, height, p, q> * p::avl<size1, height1, S1> * q::avl<size2, height2, S2> & size = 1+size1+size2 & height2<=height1+1 & height1<=height2+1 & height = max(height1, height2) + 1
  & forall (a: (a notin S1 | a < v)) & forall (a: (a notin S2 | a > v))
  & S = union (S1, S2, {v})
  inv size >= 0 & height >= 0;
*/

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

struct node * new_leaf(int value)
{
  struct node *leaf = (struct node *) malloc(sizeof(struct node));
  leaf->value = value;
  leaf->height = 1;
  leaf->left = NULL;
  leaf->right = NULL;
  return leaf;
}


int height(struct node *tree)
/*@
  case {
    tree = null  -> ensures res = 0;
    tree != null -> requires tree::node^<v,h,l,r>@L ensures res = h;
  }
*/
{
  return tree ? tree->height : 0;
}


int update_height(struct node *tree)
/*@
  requires tree::node^<v, _, l, r> * l::avl<s1, h1, N1>@L * r::avl<s2, h2, N2>@L
  ensures tree::node^<v, h, l, r> & h = max(h1, h2) + 1;
*/
{
  tree->height = MAX(height(tree->left), height(tree->right)) + 1;
}


int find_min(struct node *tree)
/*@
  requires tree::avl<s, h, N> & tree != null
  ensures tree::avl<s, h, N> &  tree != null & forall (a: (a notin N | res <= a));
*/
{
  if (tree->left == NULL)
    return tree->value;
  else
    return find_min(tree->left);
}


struct node * left_rotate(struct node *x)
{
  struct node *y = x->right;
  x->right = y->left;
  y->left = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node * right_rotate(struct node *x)
{
  struct node *y = x->left;
  x->left = y->right;
  y->right = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node * balance(struct node *tree)
{
  if (height(tree->left) - height(tree->right) > 1) {
    if (height(tree->left->left) < height(tree->left->right))
      tree->left = left_rotate(tree->left);
    tree = right_rotate(tree);
  }
  else if (height(tree->left) - height(tree->right) < -1) {
    if (height(tree->right->left) > height(tree->right->right))
      tree->right = right_rotate(tree->right);
    tree = left_rotate(tree);
  }

  return tree;
}

//struct node * insert(struct node *tree, int value)
//BUG: mona has exception when verifying this specs
/*@
  requires tree::avl<size1, h1, S1>
  ensures  tree::avl<size2, h2, S2> & S2 = union(S1, {value})
           & h2 >= h1 & h2 <= h1 + 1;
*/
/*
{
  if (tree == NULL)
    return new_leaf(value);

  if (value < tree->value)
    tree->left = insert(tree->left, value);
  else
    tree->right = insert(tree->right, value);

  update_height(tree);
  tree = balance(tree);

  return tree;
}
*/

struct node * insert(struct node *tree, int value)
//BUG: mona has exception when verifying this specs
/*@
  requires tree::avl<size1, h1, S1>
  ensures  tree::avl<size2, h2, S2> & S2 = union(S1, {value})
           & h2 >= h1 & h2 <= h1 + 1;
*/
{
  if (tree == NULL) {
    struct node *leaf = (struct node *) malloc(sizeof(struct node));
    leaf->value = value;
    leaf->height = 1;
    leaf->left = NULL;
    leaf->right = NULL;
    return leaf;
  }

  if (value < tree->value)
    tree->left = insert(tree->left, value);
  else
    tree->right = insert(tree->right, value);

  update_height(tree);
  //tree->height = MAX(height(tree->left), height(tree->right)) + 1;

  //tree = balance(tree);
  if (height(tree->left) - height(tree->right) > 1) {
    if (height(tree->left->left) < height(tree->left->right))
      tree->left = left_rotate(tree->left);
    tree = right_rotate(tree);
  }
  else if (height(tree->left) - height(tree->right) < -1) {
    if (height(tree->right->left) > height(tree->right->right))
      tree->right = right_rotate(tree->right);
    tree = left_rotate(tree);
  }


  return tree;
}

struct node * delete(struct node *tree, int value)
//BUG: with mona, couldn'n verifiy 
/*@
  requires tree::avl<size1, h1, S1>
  ensures tree::avl<size2, h2, S2> & S2 = diff(S1, {value}) & h2 - h1 <= 1 & h2 - h1 >= 0;
*/
{
  int min;

  if (tree == NULL)
    return NULL;

  if (value == tree->value) {
    if (tree->left == NULL)
      return tree->right;
    else if (tree->right == NULL)
      return tree->left;
    else {
      min = find_min(tree->right);
      tree->right = delete(tree->right, min);
      tree->value = min;
    }
  }
  else if (value < tree->value)
    tree->left = delete(tree->left, value);
  else
    tree->right = delete(tree->right, value);

  update_height(tree);
  tree = balance(tree);

  return tree;
}
