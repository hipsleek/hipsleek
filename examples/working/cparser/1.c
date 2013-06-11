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
  or (exists m3: self::node*<p> * p::node<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>
  & n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx >= d & m3 = m1-m2 & m3 >= 0 & m3 <= 1) //0 <= n1 - n2 & n1 - n2 <= 1
  inv n >= 0 & mx >= 0;
*/

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

/*@
node__star cast_general_pointer_to_node__star(void__star p)
  case {
    p = null  -> ensures res = null;
    p != null -> ensures res::node__star<q> * q::node<_,_,_,_,_>;
  }

int__star cast_general_pointer_to_int__star(void__star p)
  case {
    p = null  -> ensures res = null;
    p != null -> ensures res::int__star<i>;
  }
*/

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

    return tmp;
  }
  
}

