
struct node {
  int val;
  struct node * next;
};

/*@
ll<> == self=null
  or self::node<_,p>*p::ll<>;
*/

/*@
HeapPred H( node a).
HeapPred G( node a).
HeapPred H1( node a).
HeapPred G1( node a).
*/


int main(struct node* l)
/*
   infer [H1,G1]
   requires H1(l)
   ensures G1(l);
*/
/*
 requires l::ll<>
  ensures l=null;
*/
{

  int i=0;

  while (l)
    /*
      infer [H,G]
      requires H(l)
      ensures G(l');
     */
    /*@
      requires l::ll<>
      ensures l'=null;
     */
    {
    l = l->next;
    i++;
  }
  // dprint;
  return i;
}

