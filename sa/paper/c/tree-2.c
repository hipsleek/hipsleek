// simpler tll working example

struct node{
  struct node* parent;
  struct node* left;
  struct node* right;
};

/*@

// predicate for a non-empty tree with chained leaf list

// predicate for a non-empty tree
 tree<p> == self::node<p,_,null>
	or self::node<p,l,r> * l::tree<self> * r::tree<self>
	inv self!=null;

*/

// initializes the linked list fields
/*@
HeapPred H(node a, node@NI b).
HeapPred G(node a, node@NI b).
*/
void trav (struct node* p, struct node* x)
//@ infer [H,G] requires H(x,p) ensures G(x,p);
/*
requires x::tree<p> ensures x::tree<p>;
*/
{
  struct node* xp = x->parent;
  struct node* xl = x->left;
  struct node* xr = x->right;
  //@ assert p=xp' assume p=xp';
  if (!x->right)
    {    return ;
    }
  else
    {
      trav(x,xr);
      trav(x,xl);
    }
  return;
}
