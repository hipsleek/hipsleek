struct node{
  struct node* prev;
  struct node* next;
};

/*@
HeapPred H(node a, node@NI b).
HeapPred G(node a, node b).
*/

 void set_tail (struct node* x, struct node* y)
// requires x::node<_,_>  ensures true;
 //@ infer[H,G] requires H(x,y) ensures G(x,y);
{
  //node t = x.next;
  //assume t'=null;
   x->next = y;
}

