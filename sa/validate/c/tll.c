// simpler tll working example

struct node{
  struct node* left;
  struct node* right;
  struct node* next;
};

/* predicate for a non-empty tree with chained leaf list */
/*@
 tll<ll,lr> == self::node<_,null,lr> & self = ll
	or self::node<l,r,_> * l::tll<ll,z> * r::tll<z,lr>
	inv self!=null;
*/
/* predicate for a non-empty tree  */
/*@
 tree<> == self::node<_,null,_>
	or self::node<l,r,_> * l::tree<> * r::tree<>
	inv self!=null;
*/

// initializes the linked list fields
/*@
HeapPred H(node a, node@NI b).
HeapPred G(node a, node@NI b, node c).
*/
struct node* set_right (struct node* x, struct node* t)
//@ infer [H,G] requires H(x,t) ensures G(x,res,t);
// requires x::tree<> ensures x::tll<res,t>;
{
  if (x->right==NULL) 
    {
      x->next = t;
      return x;
    }
  else 
    {
      struct node* l_most = set_right(x->right, t);
      return set_right(x->left, l_most);
  	}
}

struct node* testhar (struct node* x, struct node* t)
{
  return set_right(x,t);
}

/*
# tll.ss --sa-dnc --pred-en-dangling --pred-en-eup


*/
