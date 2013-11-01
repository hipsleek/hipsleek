// see examples/working/hip/global-ll.c

#include <stddef.h>

struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self = null & n = 0 
  or self::node<_,p> * p::ll<n1> & n = n1 + 1
  inv n >= 0;
*/

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

/* global vars */
int n;
struct node* p;

void insert_rec(struct node* x, int a)
/*@
  requires x::ll<n1> & n1 > 0 
  ensures x::ll<n1+1>;
*/
{
  if (x->next == NULL) {
    struct node* p = malloc(sizeof(struct node));
    p->val = a;
    p->next = NULL;
    x->next = p;
  }
  else 
    insert_rec(x->next, a);
} 


void delete_last_rec(struct node* x)
/*@
  requires x::ll<n1> & n1 > 1
  ensures x::ll<n1-1>;
*/
{
  if (x->next->next == NULL)
    x->next = x->next->next;
  else
    delete_last_rec(x->next);
}

void insert(int a)
/*@
  requires p::ll<n> & n > 0
  ensures p'::ll<n'> & n'=n+1 & p=p';
*/
{
  insert_rec(p,a);
  n = n+1;
}

void delete_last()
/*@
  requires p::ll<n> & n > 1
  ensures p'::ll<n'> & n=n'+1 & p=p';
*/
{
  delete_last_rec(p);
  n = n-1;
}

void main()
/*@
  requires true
  ensures p'::ll<n'> & n'=3;
*/
{
  p = malloc(sizeof(struct node));
  p->val = 5;
  p->next = NULL;
  n=1;
  insert(4);
  insert(3);
  insert(2);
  insert(1);
  delete_last();
  delete_last();
}
