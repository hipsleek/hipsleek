struct node {
  struct node* t;
  struct node* next;
};

/*@
lsegh<t> == self=t
  or self::node<t, q> * q::lsegh<t> & self!=t
  inv true;
*/
/*@
HeapPred H(node a, node b).
HeapPred G(node a, node b).
*/
int foo(struct node* x, struct node* t)
/*
  requires x::lsegh<t>
  ensures  res=1;
*/
/*@
  infer [H,G]
  requires H(x,t)
  ensures  G(x,t) & res=1;
*/
 {
   if (x==t) return 1;
   else {
     int b1 = foo(x->next, t);
     //int b2 = x->t == t;
     return b1 && x->t == t;
   }
 }
