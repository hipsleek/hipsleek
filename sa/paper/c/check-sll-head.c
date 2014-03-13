struct node {
  struct node* h;
  struct node* next;
};

/*@
lsegh<h> == self=h
  or self::node<h, q> * q::lsegh<h> & self!=h
  inv true;
*/
/*@
HeapPred H(node a, node b).
HeapPred G(node a, node b).
*/
int foo(struct node* x, struct node* h)
/*
  requires x::lsegh<h>
  ensures  res=1;
*/
/*@
  infer [H,G]
  requires H(x,h)
     ensures  G(x,h) & res=1;
*/
 {
   if (x==h) return 1;
   else {
     int b1 = foo(x->next, h);
     // int b2 = x->h == h;
     return b1 && x->h == h;
   }
 }
