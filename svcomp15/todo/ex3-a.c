#include "stdlib.h"


struct node{int v;};


void test(struct node* x)
/*@
  requires x::node<_>
  ensures emp & true;
*/
{
  free(x);
  return;
}
