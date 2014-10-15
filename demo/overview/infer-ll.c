/* representation of a node */
struct node {
  int val;
  struct node * next;
};

/* view for a singly linked list */
/*@
ll<> == self = null
	or self::node<_, q> * q::ll<>
	inv true;
*/

/*@
HeapPred H(node a).
HeapPred G(node b).
 */

int length(struct node* x)
// requires x::ll<> ensures x::ll<> ;
//@  infer [H,G] requires H(x) ensures G(x);
{
  if (x == NULL) return 0;
  else return (1+length(x->next));
}

