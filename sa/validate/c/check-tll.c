// simpler tll working example

struct node{
	struct node* left;
	struct node* right;
	struct node* next;
};

/* predicate for a non-empty tree with chained leaf list */
/*@
 tll<ll,lr> == self::node<null,null,lr> & self = ll
	or self::node<l,r,_> * l::tll<ll,z> * r::tll<z,lr>
	inv self!=null;
*/
/* predicate for a non-empty tree  */
/*@
 tree<> == self::node<null,null,_>
	or self::node<l,r,_> * l::tree<> * r::tree<>
	inv self!=null;

*/
// initializes the linked list fields
/*@
HeapPred H( node a, node@NI b, node@NI c).
HeapPred G( node a, node@NI b, node@NI c).
*/

int check_tll(struct node* x,struct node* t,struct node* r)
/*@
  infer [H,G] requires H(x,t,r) ensures G(x,t,r) & res=1;//'
//  requires x::tll<t,ggg>@L ensures res=1 & r'=ggg;//'
*/
{
  if (x->right==NULL && x->left==NULL)
    {
      r = x->next;
      return 1;
    }
  else
    {
      if (x->left==NULL || x->right==NULL ) return 0;
      struct node* r_most;
      int b = check_tll(x->left, t, r_most);
      return b && check_tll(x->right, r_most, r);
    }
}

/*
# check-tll.ss --sa-dnc --pred-en-dangling

*/
