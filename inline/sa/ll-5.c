#include <stdio.h>
struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self=null & n=0
  or self::node<_,p>*p::ll<n-1>
  inv n>=0;
*/

/*@
HeapPred H( node a).
HeapPred G( node a).
HeapPred H1( node a).
HeapPred G1( node a).
*/

//requires x::ll<>
// ensures  x::ll<>;
/*
 infer [H,G]
  requires H(x)
 ensures  G(x);
*/
int foo(struct node* x)
/*@
 requires x::ll<n>
 ensures  x::ll<n> & res=n;
*/
 /*
 infer [H,G]
  requires H(x)
 ensures  G(x);
*/
 {
   if (!x) {
     return 0;
   }
   else
     return 1+foo(x->next);
 }

int main()
/*@
 requires true
 ensures  res=1;
*/
{
  struct node p;
  //p.next=0;
  int m = foo(&p);
  //printf("m = %i\n",m);
  return m;
}

/*

why List.combine error?

*/


