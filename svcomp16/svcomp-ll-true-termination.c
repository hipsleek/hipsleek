#include "../examples/working/cparser/stdhip.h"
struct node {
  int val;
  struct node* next;
}; 

struct node* new_ll(int n)
{
  if (n==0)
    return NULL;
  struct node *x = malloc(sizeof *x);
  x->next = new_ll(n-1);
  return x;
}

void main()
{
  struct node *xs = new_ll(10);
  while (xs != NULL)
  {
     xs = xs->next;
  }
}
