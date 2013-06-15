/* priority queues */
#include <stddef.h>

struct node {
  int val;
  int nleft;
  int nright;
  struct node* left;
  struct node* right;
};

/*@
pq<n, mx> == self = null & n = 0 & mx = 0 
  or (exists m3: self::node^<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>
  & n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx >= d & m3 = m1-m2 & m3 >= 0 & m3 <= 1)
  inv n >= 0 & mx >= 0;
*/

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

/* function to insert an element in a priority queue */
struct node* insert(struct node* t, int v)
/*@
  requires t::pq<n, mx> & v >= 0
  ensures res::pq<n1, ma> & n1 = n+1 & (v>=mx & ma = v | ma = mx);
*/
{
  struct node* tmp; 
  int tmpv;

  if (t == NULL) {
    struct node* p = malloc(sizeof(struct node));
    p->val = v;
    p->nleft = 0;
    p->nright = 0;
    p->left = NULL;
    p->right = NULL;
    return p;
  }
  else
    if (v > t->val)
    {
      if (t->nleft <= t->nright)
      {
        tmp = t->left;
        tmpv = t->val;
        t->left = insert(tmp, tmpv);
        tmpv = t->nleft;
        t->nleft = tmpv + 1;
      }
      else 
      {
        tmp = t->right;
        tmpv = t->val;
        t->right = insert(tmp, tmpv);
        tmpv = t->nright;
        t->nright = tmpv + 1;
      }
      t->val = v;
      return t;
    }
    else
    {
      if (t->nleft <= t->nright)
      {
        tmp = t->left;
        t->left = insert(tmp, v);
        tmpv = t->nleft;
        t->nleft = tmpv + 1;
      }
      else 
      {
        tmp = t->right;
        t->right = insert(tmp, v);
        tmpv = t->nright;
        t->nright = tmpv + 1;
      }
      return t;
    }
}



/* function to delete a leaf */
int deleteoneel(struct node* t)
/*@
  requires t::pq<n, mx> & n > 0
  ensures t::pq<n-1, mx2> & 0 <= res <= mx & mx2 <= mx;
*/
{
  int v;

  if ((t->nleft == 0) && (t->nright == 0))
  {
    v = t->val; 
    t = NULL;
    return v;
  }
  else 
  {
    int tmp;

    int* tnleft = malloc(sizeof(int));
    int* tnright = malloc(sizeof(int));
    struct node* tleft = malloc(sizeof(struct node));
    struct node* tright = malloc(sizeof(struct node));
    
    *tnleft = t->nleft;
    *tnright = t->nright;
    tleft = t->left;
    tright = t->right;
    
    tmp = deleteone(tnleft, tnright, tleft, tright);

    return tmp;
  }
}

/* function to delete one element */
int deleteone(int* m1, int* m2, struct node* l, struct node* r)
/*@
  requires m1::int^<im1> * m2::int^<im2> * l::pq<im1, mx1> * r::pq<im2, mx2> & im1 + im2 > 0 & 0 <= im1 - im2 <=1
  ensures m1::int^<am1> * m2::int^<am2>  * l::pq<am1, mx3> * r::pq<am2, mx4> & am1 + am2 + 1 = im1 + im2 & 0 <= am1 - am2<= 1 
    & mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi;
*/
{
  if (*m1 > *m2)
  {
    *m1 = *m1 - 1;
    return deleteoneel(l);
  }
  else 
  {
    *m2 = *m2 - 1;
    return deleteoneel(r);
  }
}

/* function to restore the heap property */
void ripple(int* d, int v, int m1, int m2, struct node* l, struct node* r)
/*@
  requires l::pq<m1, mx1> * r::pq<m2, mx2> * d::int^<id> & 0 <= m1 - m2 <= 1 & id >= mx1, mx2 & 0 <= v <= id
  ensures l::pq<m1, mx3> * r::pq<m2, mx4> * d::int^<ad> & mx3 <= mx1 & mx4 <= mx2 & 
  max1 = max(mx1, v) & max2 = max(mx2, max1) &  
    ad <= max2 & ad >= mx3, mx4, 0;
*/

{
  if (m1 == 0)
      { //assume false;
    if (m2 == 0)
    {
      *d = v;
    }
  }
  else
  {
    if (m2 == 0)
    {
      //assume false;
      if (v >= l->val)
        *d = v;
      else
      {
        *d = l->val;
        l->val = v;
      }
    }
    else 
    {
      if (l->val >= r->val)
      {
        if (v >= l->val)
          *d = v;
        else 
        {   //assume false;
          *d = l->val;
          ripple(d, v, l->nleft, l->nright, l->left, l->right);
        }
      }
      else
      {
        if (v >= r->val)
          *d = v;
        else
        {  //assume false;
          //dprint;
          *d = r->val;
          ripple(d, v, r->nleft, r->nright, r->left, r->right);
        }
      }
    }
  }
}


/* function to delete the root of a heap tree */
int deletemax(struct node* t)
/*@
  requires t::pq<n, mx> & n > 0 
  ensures t::pq<n-1, mx2> & mx2 <= res <= mx;
*/
{
  int v, tmp;

  if ((t->nleft == 0) && (t->nright == 0))
  {
    tmp  = t->val;
    t = NULL;
    return tmp;
  }
  else
  {
    
    int* tval = malloc(sizeof(int));
    int* tnleft = malloc(sizeof(int));
    int* tnright = malloc(sizeof(int));

    struct node* tleft = malloc(sizeof(struct node));
    struct node* tright = malloc(sizeof(struct node));
    
    *tval = t->val;
    *tnleft = t->nleft;
    *tnright = t->nright;
    tleft = t->left;
    tright = t->right;
    
    v = deleteone(tnleft, tnright, tleft, tright);
    tmp = *tval;
    ripple(tval, v, *tnleft, *tnright, tleft, tright);

    return tmp;
  }
  
}
