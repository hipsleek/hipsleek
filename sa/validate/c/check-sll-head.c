struct node {
  struct node* h;
 struct node* next;
};

/*@
lsegh<h> == self=h
  or self::node<h, q> * q::lsegh<h>
  inv true;
*/
/*@
HeapPred H(node a, node@NI b).
HeapPred G(node a, node b).
*/
int foo(struct node* x, struct node* h)
/*
  requires x::lsegh<h>
  ensures  res>0;
*/
/*@
  infer [H,G]
  requires H(x,h)
  ensures  G(x,h) & res=1;
*/
 {
   if (x==h) return 1;
   else {
     /* int b1 = foo(x->next, h); */
     /* if (b1) { */
     /* int b2 = x->h == h; */
     /* return b2; */
     /* } else return 0; */
     return foo(x->next, h) &&
       (x->h == h);
   }
 }

/*
{local: int tmp,int tmp___0
int tmp;
int tmp___0;
(73, ):if (x == h) {
  (73, ):(86, ):return 1;
} else {
  (73, ):{tmp = (75, ):foo(member access x~~>next, h);
(77, ):if ((84, ):bool_of_int___(tmp)) {
  (77, ):(79, ):if (member access x~~>h == h) {
  (79, ):tmp___0 = 1;
} else {
  (79, ):tmp___0 = 0
};
} else {
  (77, ):tmp___0 = 0
};
(85, ):return tmp___0}
}}

 */
