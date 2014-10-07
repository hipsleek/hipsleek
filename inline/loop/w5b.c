struct node {
  int val;
  struct node* next;
};

/*@
ll<> == self=null
  or self::node<_,p>*p::ll<>;
*/

/*@
HeapPred H( node a).
HeapPred G( node a).
*/

int main(struct node* l)
/*@
  requires l::ll<>
  ensures l::ll<> & res<=11;
*/
{
  int i = 0;
  for (i = 0; i <= 10 && l != NULL;)
    /*
      infer [H,G]
      requires H(l)
      ensures G(l');
     */
    /*@
      requires l::ll<>
      ensures l::ll<> & i'<=11;
    */
    {
    i++;
    l = l->next;
  }
  return i;
}
