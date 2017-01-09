struct node {
  int val; 
  struct node* next;	
};

/* view for a singly linked list */
/*@
ll<> == self = null
	or self::node<_, q> * q::ll<>
  inv true;
*/
/*@
HeapPred H1(node a).
HeapPred G1(node a).

HeapPred H2(node a).
HeapPred G2(node a).
*/
int bubble(struct node* xs)
  /* requires xs::node<_,p> * p::ll<> 
   ensures  xs::node<_,p1> *p1::ll<>; */
/*@
  infer[H1,G1]
  requires H1(xs)
  ensures G1(xs);
*/
{
  int aux, tmp1;
  int tmp, flag; 
  
  if (xs->next == NULL) {
    return 0;
  }
  else {
    tmp = bubble(xs->next);
    int xv = xs->val;
    int xnv = xs->next->val;
    if (xv <= xnv) 
      flag = 0;
    else {
      xs->val = xnv;
      xs->next->val = xv; //ERROR: lhs and rhs do not match
      flag = 1; 
    }
    //dprint;
    return (flag || tmp);
  }
}

void bsort(struct node* xs)
  /* requires xs::node<_,p>*p::ll<> 
   ensures xs::node<_,p1> * p1::ll<>; */
/*@
  infer[H2,G2]
  requires H2(xs)
  ensures G2(xs);
*/
{
  int b;

  b = bubble(xs);
  if (b) {
    bsort(xs);
  }
}
