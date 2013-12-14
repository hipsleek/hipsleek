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

/*
ll<n> == self=null & n=0
  or self::node<_,q>*q::node__star<r>*r::ll<n-1>
  inv n>=0;


ll<n> == self=null & n=0
  or self::node^<_,q>*q::ll<n-1>
  inv n>=0;

ll<n> == self=null & n=0
  or self::node__star<r>*r::node<_,q>*q::ll<n-1>
  inv n>=0;
*/

int foo(struct node* q)
/*
  requires q::node__star<r>*r::ll<n>
  ensures q::node__star<r>*r::ll<n>;
*/
{
  if (q) return 0;
  else return 1+foo(q->next);
}

int foo2(struct node *q)
/*
  requires q::ll<n>
  ensures q::ll<n>;
*/
{
  struct node* tmp = q;
  if (tmp) return 0;
  else return 1+foo2((*q).next);
}

void main() 
/*@
 requires true
 ensures true;
*/
{
  int x=1;
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

