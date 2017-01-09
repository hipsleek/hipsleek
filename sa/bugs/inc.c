
#include "inc.h"


struct node* update_next(struct node* x)
{
  struct node* p = get_next(x);
  p = NULL;
  return x;
}

struct node* get_next(struct node* x)
{
  return x->next;
}

