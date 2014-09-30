struct node{
  struct node* prev;
  struct node* next;
};

/*@
dll<p> == self = null or self::node<p,x> * x::dll<self> & self!=null;
*/

/*@
PostPred G(node a,node b).
HeapPred H(node a,node b).
*/

void dll_append(struct node* x, struct node* y)
//@ infer [H,G] requires H(x,y) ensures G(x,y);
// requires x::dll<p> * y::dll<_> & x!=null &y!=null ensures x::dll<p>;
{
  if (x->next) {
    dll_append(x->next,y);
  }
  else{
    x->next = y;
    y->prev = x;
  }
}
