struct node {
  int val;
  struct node* left;
  struct node* right;
  struct node* parent;
};

/*
 * predicate describes binary search tree data structure
 */
/*@
bstree <C> ==
     self = null & C = {}
     or self::node<v,l,r,_> * l::bstree<Cl> * r::bstree<Cr>
        & C = union({v}, Cl, Cr)
        & forall (x: (x notin Cl | x < v))
        & forall (x: (x notin Cr | x > v));
*/

/*
 * Return max node and update new root in parameter "new_root"
 */
struct node* extract_max(struct node* root, struct node **c)
/*@
  requires root::bstree<C> * c::node*<_> & root != null
  ensures c::node*<p> * p::bstree<C1> * res::node<rv,_,null,null>
          & C = union(C1,{rv}) & forall (x: (x notin C1) | x < rv);
*/
{
  struct node* m;
  if (root->right != NULL) {
    m = extract_max(root->right, c);
    root->right = *c;
    if (*c != NULL)
      (*c)->parent = root;
    *c = root;
    return m;
  }
  else {
    *c = root->left;
    root->parent = NULL;
    return root;
  }
}
