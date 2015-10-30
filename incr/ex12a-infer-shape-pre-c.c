/* singly linked lists */

/* representation of a node */
struct node {
  int val;
  struct node* next;
};

/*@

sll<> == self = null 
	or self::node<_, q> * q::sll<>
  inv true;

HeapPred H(node a).
//HeapPred G(node a, node b).
HeapPred H1(node a).
*/

int size_helper(struct node* x)
/*
  infer[H]
  requires H(x)  ensures true;//H1(x);
*/
//@  infer[@shape_pre] requires true ensures true;

{
  if (x==NULL) 
    return 0;
  else {
    return 1+ size_helper(x->next);
  }
}


