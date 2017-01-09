#include <stddef.h>

struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self = null & n = 0 
  or self::node*<r> * r::node<_,p> * p::ll<n1> & n = n1 + 1
  inv n >= 0;
*/


void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;


/* insert an item to the end of current list */
void insert_last (struct node* x, int a)
/*@
  requires x::ll<n> & n > 0
  ensures x::ll<n+1>;
*/
{
  if (x->next == NULL)
  {
    struct node* p = malloc(sizeof(struct node));
    x->val = a;
    x->next = NULL;
    x->next = p;
  }
  else
  {
    insert_last(x->next, a);
  }
}

void insert(struct node** x, int a)
/*
  requires x::ll^<n> & n >= 0
  ensures x::ll^<n+1>;
*/
{
  insert_last(*x, a);
}
