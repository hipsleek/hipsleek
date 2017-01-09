#include "../bugs/inc.h"

struct node* get_next(struct node* x)
{
  struct node* tmp = x;
  return tmp->next;
}

