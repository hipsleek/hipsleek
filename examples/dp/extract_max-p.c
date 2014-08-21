struct node {
  int val;
  struct node* left;
  struct node* right;
  struct node* parent;
};


struct pair {
  struct node* new_root;
  struct node* max_node;
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

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

/*
 * Return a pair of new root and max node
 */
struct pair extract_max(struct node* root)
/*@
  requires root::bstree<C> & root != null
  ensures res::pair<nr,nm> * nr::bstree<C1> * nm::node<rv,_,null,null>
          & C = union(C1,{rv}) & forall (x: (x notin C1) | x < rv);
*/
{
  struct node *m, *c;
  if (root->right != NULL) {
    struct pair r = extract_max(root->right);
    c = r.new_root;
    m = r.max_node;
    root->right = c;
    if (c != NULL) c->parent = root;
    r.new_root = root;
    r.max_node = m;
    return r;
  }
  else {
    c = root->left;
    root->parent = NULL;
    struct pair r;
    r.new_root = c;
    r.max_node = root;
    return r;

  }
}
