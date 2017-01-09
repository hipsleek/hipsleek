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

 gtree<p> == self=null 
        or self::node<p,l,r> * l::gtree<self> * r::gtree<self>
	 inv true;
*/

// initializes the linked list fields
/*
HeapPred H(node a, node@NI b).
HeapPred G(node a, node@NI b, node c).
*/
void trav (struct node* p, struct node* x)
//infer [H,G] requires H(x,t) ensures G(x,res,t);
/*@
//requires x::tree<p> ensures x::tree<p>;
requires x::gtree<p> ensures x::gtree<p>;
*/
{
   __VERIFIER_plot("dll-concat-lists-0001");
  struct node* xp = x->parent;
  struct node* xl = x->left;
  struct node* xr = x->right;
  //@ assert p=xp' assume p=xp';
  if (!x->right)
    {
      //		assert xl'=null;
      ;
    }
  else
    {
//		assert xr'!=null & xl'!=null;
      trav(x,xr);
      trav(x,xl);
    }
  __VERIFIER_plot("tree");
}

int main()
{
  struct node* p;
  struct node* x;
  trav (p, x);
  return 1;
}

/*





*/
