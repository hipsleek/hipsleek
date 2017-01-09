#include <stddef.h>
// star_fields
struct node {
  int x;
  struct node* next;
};

/*@
ll<n> == self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;
*/

int foo(struct node* q)
/*
  requires q^::ll<n>
  ensures q^::ll<n>;
*/
{
  struct node* tmp = q;
  if (tmp) return 0;
  else return 1+foo(q->next);
}

void main() 
/*@
 requires true
 ensures true;
*/
{
  struct node q = {1, NULL};
  int t1 = foo(&q);
  struct node* qq;
  int t2 = foo(qq);
}

/*
int star_foo(node star_q)
  requires *q::ll<n>
  ensures *q::ll<n>;
{
  if (star_q==0) return 0;
  else return 1+star_foo(star_q.next);
}
*/

