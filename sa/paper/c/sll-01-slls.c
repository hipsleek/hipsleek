#include "../../../examples/working/cparser/stdhip.h"

struct node_low {
    struct node_low* next;
};

struct node_top {
    struct node_top* next;
    struct node_low* data_;
};

struct node_top* alloc_node_top()
/*@
 requires true
  ensures res::node_top<_,_> ;
*/
{
   return malloc(sizeof(struct node_top));
}

struct node_low* alloc_node_low()
/*@
 requires true
  ensures res::node_low<_> ;
*/
{
   return malloc(sizeof(struct node_low));
}

struct node_top* create_top()
/*@
  requires true
  ensures res::node_top<null,null>;
*/
{
  struct node_top* ptr = alloc_node_top();//new node_top(null, null);
  ptr->next = NULL;
  ptr->data_ = NULL;
  return ptr;
}

struct node_low* create_low()
/*@
  requires true
  ensures res::node_low<null>;
*/
{
  struct node_low* ptr = alloc_node_low();//new node_low(null);
  ptr->next = NULL;
  return ptr;
}

int get_nondet()
/*@
  requires true
  ensures true;
*/
{
  return 1;
}

struct node_top* alloc()
/*@
  requires true
   ensures res::node_top<null,l> & l=null
   or res::node_top<null,l> * l::node_low<null>;
*/
{
    struct node_top* pi = create_top();
    if (get_nondet())
        pi->data_ = create_low();

    return pi;
}
/*@
ll<> == self = null
  or self::node_top<p, r> * p::ll<> & self != null  & r=null
  or self::node_top<p, r> * p::ll<> * r::node_low<null> & self != null;
*/
/*@
HeapPred H(node_top a).
*/
struct node_top* helper ()
 /* requires true 
   ensures res::ll<>; */
/*@
 infer[H]
 requires true
  ensures H(res);
*/
{
  struct node_top* tmp, *x;
  if (get_nondet()) return NULL;
  else {
    tmp = helper();
    x = alloc();
    x->next = tmp;
    return x;
  }
}

/*
 node_top create_sll(node_top x)
{
    node_top sll = alloc();
    node_top *now = sll;

    // NOTE: running this on bare metal may cause the machine to swap a bit
    int i;
    for (i = 1; i; ++i) {
        now->next = alloc();
        now = now->next;
    }

    return sll;
}
*/
