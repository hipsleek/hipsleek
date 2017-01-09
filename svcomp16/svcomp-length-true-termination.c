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

int length(struct node* xs)
{
  if (xs == NULL) 
    return 0;
  return (1+length(xs->next));
}

void main()
{
  struct node *xs = new_ll(10);
  return (length(xs));
}
