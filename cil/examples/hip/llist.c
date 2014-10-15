#include <stddef.h>

struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self = null & n = 0 
  or self::node^<_,p> * p::ll<n1> & n = n1 + 1
  inv n >= 0;
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
    p != null -> ensures res::node^<_,_>;
  }
*/


/* insert an item to the end of current list */
void insert_last (struct node* x, int a)
/*
  requires x::ll<n> & n > 0
  ensures x::ll<n+1>;
*/
{
  if (x->next == NULL)
  {
    struct node* p = malloc(sizeof(struct node));
    p->val = a;
    p->next = NULL;
    x->next = p;
  }
  else
  {
    insert_last(x->next, a);
  }
}

void delete_last(struct node* x)
/*@
  requires x::ll<n> & n > 1
  ensures x::ll<n-1>;
*/
{
  if (x->next->next == NULL)
  {
    // need free node x->next before reassign it
    x->next = x->next->next;
  }
  else
    delete_last(x->next);
}
