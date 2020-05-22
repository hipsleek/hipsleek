#include <stdio.h>
#include <stdlib.h>

struct node {
  int val;
  struct node* next;
};
struct node* createNode(int data, struct node* x)
/*@
  requires emp & true
  ensures res::node<data, next>
*/
{
	struct node* new_node = (struct node*) malloc(sizeof(struct node));
	new_node->next = x;
	new_node->data = data;
	return new_node;
}


/*@
  ll<n> == self=null & n = 0
  or self::node<_, r> * r::ll<n2> & n = 1 + n2 & n > 0
  inv n >= 0;
*/


struct node* copy(struct node* x)
/*@
  requires x::ll<n>
  ensures res::ll<n> * x::ll<n>;
*/
{
  if (x == NULL) return x;
  else {
    struct node* tmp;
    tmp = copy(x -> next);
    return createNode(x -> val, tmp);
  }
}
