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
  or (exists m3: self::node<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>
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
    return v;
  }
  else 
  {
    int* tnleft = malloc(sizeof(int));
    int* tnright = malloc(sizeof(int));
    struct node* tleft;
    struct node* tright;
    
    *tnleft = t->nleft;
    *tnright = t->nright;
    tleft = t->left;
    tright = t->right;
    
    int tmp = deleteone(tnleft, tnright, tleft, tright);

    return tmp;
  }
}

/* function to delete one element */
int deleteone(int* m1, int* m2, struct node* l, struct node* r)
/*@
  requires m1::int^<im1> * m2::int^<im2> * l::pq<im1, mx1> * r::pq<im2, mx2> & im1 + im2 > 0 & 0 <= im1 - im2 <=1
  ensures m1::int^<am1> * m2::int^<am2>  * l::pq<am1, mx3> * r::pq<am2, mx4> & am1 + am2 + 1 = im1 + im2 & 0 <= am1 - am2<= 1 
    & mx3 <= mx1 & mx4 <= mx2 & (0 <= res <= mx1 | 0 <= res <= mx2);
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
