/* avl trees */

/* representation of a node in an avl tree */
struct node {
  int val;
  int height;
  struct node* left;
  struct node* right;
};

/* view for avl trees */
/*@
avl<size, height> == self = null & size = 0 & height = 0 
  or self::node^<_, height, p, q> * p::avl<size1, height1> * q::avl<size2, height2> & size = 1+size1+size2 & height2<=height1+1 & height1<=height2+1 & height = max(height1, height2) + 1 
  inv size >= 0 & height >= 0;
*/

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

/* function to return the height of an avl tree */
int height(struct node* x)
/*@
  requires x::avl<m, n>
  ensures x::avl<m, n> & res = n; 
*/
{
  if (x == NULL)
    return 0;
  else
    return x->height;        
}

/*  function to rotate left */
struct node* rotate_left(struct node* l, struct node* rl, struct node* rr)
/*@
  requires l::avl<lm, ln> * rl::avl<rlm, ln> * rr::avl<rrm, ln+1>
  ensures res::avl<2+lm+rlm+rrm, 2+ln>; 
*/
{
  int v = 10, h;
  
  h = height(l) + 1;
  struct node* tmp = malloc(sizeof(struct node));
  tmp->val = v;
  tmp->height = h;
  tmp->left = l;
  tmp->right = rl;

  h = h + 1;
  struct node* tmp2 = malloc(sizeof(struct node));
  tmp2->val = v;
  tmp2->height = h;
  tmp2->left = tmp;
  tmp2->right = rr;
  return tmp2;
}


/* function to rotate right */
struct node* rotate_right(struct node* ll, struct node* lr, struct node* r)
/*@
  requires ll::avl<llm, lln> * lr::avl<lrm, lln - 1> * r::avl<rm, lln - 1> 
  ensures res::avl<2 + llm + lrm + rm, 1 + lln>; 
*/
{
  struct node* tmp; 
  int v = 10, h;
  
  h = height(r) + 1;
  struct node* tmp = malloc(sizeof(struct node));
  tmp->val = v;
  tmp->height = h;
  tmp->left = lr;
  tmp->right = r;
  
  h = h + 1;
  struct node* tmp2 = malloc(sizeof(struct node));
  tmp2->val = v;
  tmp2->height = h;
  tmp2->left = ll;
  tmp2->right = tmp;
  return tmp2;
}

int get_max(int a , int b)
/*@
  requires true 
  ensures res = max(a, b);
*/
{
  if (a >= b)
    return a;
  else
    return b;
}


/* double left rotation */
struct node* rotate_double_left(struct node* a, struct node* b, struct node* c, struct node* d, int v1, int v2, int v3)
/*@
  requires a::avl<am, an> * b::avl<bm, bn> * c::avl<cm, cn> * d::avl<dm, an> & an = max(bn, cn) 
           & -1 <= bn - cn <= 1
  ensures res::avl<3 + am + bm + cm + dm, an + 2>;
*/
{
  int h;

  h = get_max(height(a), height(b));
  h = h + 1;
  struct node* tmp1 = malloc(sizeof(struct node));
  tmp1->val = v1;
  tmp1->height = h;
  tmp1->left = a;
  tmp1->right = b;

  h = get_max(height(c), height(d));
  h = h + 1;
  struct node* tmp2 = malloc(sizeof(struct node));
  tmp2->val = v3;
  tmp2->height = h;
  tmp2->left = c;
  tmp2->right = d;

  h = get_max(height(tmp1), height(tmp2));
  h = h + 1;
  struct node* tmp3 = malloc(sizeof(struct node));
  tmp3->val = v2;
  tmp3->height = h;
  tmp3->left = tmp1;
  tmp3->right = tmp2;
  return tmp3;
}


/* double right rotation */
struct node* rotate_double_right(struct node* a, struct node* b, struct node* c, struct node* d, int v1, int v2, int v3)
/*@
  requires a::avl<am, an> * b::avl<bm, bn> * c::avl<cm, cn> * d::avl<dm, an> 
           & an = max(bn, cn) & -1 <= cn - bn <= 1
  ensures res::avl<3 + am + bm + cm + dm, 2 + an>;
*/
{
  int h;

  h = get_max(height(a), height(b));
  h = h + 1;
  struct node* tmp1 = malloc(sizeof(struct node));
  tmp1->val = v3;
  tmp1->height = h;
  tmp1->left = a;
  tmp1->right = b;

  h = get_max(height(c), height(d));
  h = h + 1;
  struct node* tmp2 = malloc(sizeof(struct node));
  tmp2->val = v1;
  tmp2->height = h;
  tmp2->left = c;
  tmp2->right = d;

  h = get_max(height(tmp1), height(tmp2));
  h = h + 1;
  struct node* tmp3 = malloc(sizeof(struct node));
  tmp3->val = v2;
  tmp3->height = h;
  tmp3->left = tmp1;
  tmp3->right = tmp2;
  return tmp3;

}


/* functions to build avl trees */
struct node* build_avl1(struct node* x, struct node* y)
/*@
  requires x::avl<mx, nx> * y::avl<my, nx> & x != null
  ensures res::avl<1 + mx + my, 1 + nx>;
*/
{
  int v = 0;
  int h;

  h = x->height;
  h = h + 1;
  
  struct node* tmp = malloc(sizeof(struct node));
  tmp->val = v;
  tmp->height = h;
  tmp->left = x;
  tmp->right = y;
  return tmp;  
}

void build_avl2(struct node* x, struct node* y, struct node* z)
/*@
  requires y::avl<my, ny> * z::avl<mz, ny> * x::node^<_, _, _, _> & y != null
  ensures  x::avl<1 + my + mz, 1 + ny>;
*/
{
  int tmp;

  x->left = y;
  x->right = z;
  x->height = y->height  + 1;
}

struct node* node_error() __attribute__ ((noreturn))
/*@
  requires true
  ensures false;
*/;

/* function to insert a struct node* in an avl tree (using the rotate functions) */
struct node* insert(struct node* x, int a)
/*@
  requires x::avl<m, n>
  ensures res::avl<m+1, _>;
*/
{
  if (x == NULL) {
    struct node* tmp = malloc(sizeof(struct node));
    tmp->val = a;
    tmp->height = 1;
    tmp->left = NULL;
    tmp->right = NULL;
    return tmp;
  }
  else 
  {
    if (a <= x->val)
    {
      x->left = insert(x->left, a);
      // check if we need rotation 
      if ((height(x->left) - height(x->right)) == 2)
      {
        if (height(x->left->left) > height(x->left->right))
        {
          return rotate_right(x->left->left, x->left->right, x->right);
        }
        else
        {
          if (height(x->left->left) == (height(x->left->right) - 1))
            return rotate_double_left(x->left->left, x->left->right->left, x->left->right->right, x->right, 1, 1, 1);
          else
            return node_error();
        }
      }
      else
        return node_error();
    }
    else
    {
      x->right = insert(x->right, a);
      if ((height(x->right) - height(x->left)) == 2)
      {
        if (height(x->right->right) > height(x->right->left))
        {
          return rotate_left(x->left, x->right->left, x->right->right);
        }
        else
        {
          if ((height(x->right->left) - 1) == height(x->right->right))
            return rotate_double_right(x->left, x->right->left->left, x->right->left->right, x->right->right, 1, 1, 1);
          else
            return node_error();
        }
      }
      else 
        return node_error();
    }
  }
}

/* function to insert in an avl tree (inline version) */
struct node* insert_inline(struct node* x, int a)
/*@
  requires x::avl<m, n> 
  ensures res::avl<m + 1, n1> & n <= n1 <= n+1;
*/
{
  struct node* k1, *k2;
  int h, hl, hr, hlt;

  if (x == NULL) {
    struct node* tmp = malloc(sizeof(struct node));
    tmp->val = a;
    tmp->height = 1;
    tmp->left = NULL;
    tmp->right = NULL;
    return tmp;
  }
  else
  {
    if (a <= x->val)
    { 
      x->left = insert_inline(x->left, a);
      if ((height(x->left) - height(x->right)) == 2)
      {
        k1 = x->left;
        if (height(k1->left) > height(k1->right))
        {//SRR
          x->left = k1->right;
          h = get_max(height(k1->right), height(x->right)); 
          k1->right = x; 
      
          h = h + 1;
          x->height = h;
          h = get_max(height(k1->left), h);
          h = h + 1;
          k1->height = h;
          
          return k1;          
        }
        else
        {//DLR
          if (height(k1->left) == (height(k1->right) - 1))
          {
            k2 = k1->right;
            x->left = k2->right;
            k1->right = k2->left;
            hr = height(k2->left);
            k2->left = k1; 
            hlt = height(k2->right);
            k2->right = x; 
            
            hl = height(k1->left);
            h = get_max(hl, hr);
            h = h + 1;
            k1->height = h;

            hr = height(x->right); 
            h = get_max(hlt, hr);
            h = h + 1;
            x->height = h;

            h = get_max(height(k1), x->height);
            h = h + 1;
            k2->height = h;
        
            return k2; 
          }
          else 
            return node_error();
        }
      }
      else 
        return node_error();
    }
    else  // right branch 
    {
      x->right = insert_inline(x->right, a);
      if ((height(x->right) - height(x->left)) == 2)
      {
        k1 = x->right;
        if (height(k1->right) > height(k1->left))
        {// SLR
          x->right = k1->left;
          hr = height(k1->left);
          k1->left = x; 

          hl = height(x->left);
          h = get_max(hr, hl);
          h = h + 1;
          x->height = h;
        
          hr = height(k1->right);
          h = get_max(height(x), hr);
          h = h + 1;
          k1->height = h;
        
          return k1;
        }
        else
        { // DRR 
          if ((height(k1->left) - 1) == height(k1->right))
          {
            k2 = k1->left;
            
            x->right = k2->left;
            k1->left = k2->right;
            hr = height(k2->left);
            k2->left = x;
            hlt = height(k2->right);
            k2->right = k1;

            hl = height(x->left);
            h = get_max(hl, hr);
            h = h + 1;
            x->height = h;

            hr = height(k1->right);
            h = get_max(hlt, hr); 
            h = h + 1;
            k1->height = h;

            h = get_max(height(x), height(k1));
            k2->height = ++h;
          
            return k2;
          } 
          else
            return node_error();
        }       
      }
      else 
        return node_error();
    }
  }
}

struct node* merge(struct node* t1, struct node* t2)
/*@
  case {
        t1=null -> requires t2::avl<s2,h2> ensures res::avl<s2,h2>;
        t1!=null -> requires t1::avl<s1,h1> * t2::avl<s2,h2> ensures res::avl<s1+s2,_>;
  }
*/
{
  if (t1 == NULL)
    return t2;
  else {
    struct node* tmp = insert(t2, t1->val);
    struct node* tmp1 = merge (tmp, t1->left);
    return merge(tmp1, t1->right);
  }
}

