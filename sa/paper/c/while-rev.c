struct node {
  int val;
  struct node* next;
};
/*@
ll<> == self = null  
	or self::node<_, q>* q::ll<> 
  inv true;
*/
/*@
HeapPred HX(node a).
HeapPred HY(node a).
HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G1(node a, node b,node a, node b).
*/


void reverse(struct node* x, struct node* y)
/* requires x::ll<> * y::ll<>
    ensures true; */
/*@
  infer[H1,H2]
  requires H1(x)*H2(y)
  ensures true;
*/
//requires x::ll<>
//  ensures  x'=null; //'
 /* requires x::ll<> * y::ll<> */
 /* ensures y'::ll<> & x'=null; */
 /*  FAIL
    requires x::ll<> & x=y
    ensures y'::ll<> & x'=null;
 */
{
  while(x)
    /*@
      infer[HX,HY,G1]
      requires HX(x)*HY(y)
      ensures G1(x,x',y,y');
    */
    /* requires x::ll<> * y::ll<>
      ensures y'::ll<> & x'=null; */
    {
      struct node *tmp = x->next;
      x->next = y;
      y = x;
      x = tmp;
      //reverse(x,y);
    }
  return;
}
