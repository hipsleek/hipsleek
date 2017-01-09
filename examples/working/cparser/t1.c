#include <stddef.h>

struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self=null & n=0
  or self::node<_, q> * q::ll<n-1>
  inv n>=0;
*/

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

int foo(int N)
/*@
  requires true
  ensures res=N;
  **/
{
  int i = 0;
  while (i < N) 
  /*@
    requires true
    ensures i'=N;
  */
  {
    i = i+1;
  }
  return i;
}

struct node* f(int x)
/*@
  requires true
  ensures res::ll<1> & x>0
       or res::ll<2> & x<=0;
*/
{
  struct node* y = malloc(sizeof(struct node));
  if (x > 0) {
    y->val = 0;
    y->val = 1;
    y->next = NULL;
  }
  else {
    struct node z = {6, NULL};
    y->val = 5;
    y->next = &z;
  };
 //dprint;
  return y;
}
