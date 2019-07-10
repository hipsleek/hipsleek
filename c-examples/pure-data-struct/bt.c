struct node3 {
  int val;
  struct node3* left;
  struct node3* right;
} node3;

//bt<n,h,s> == self=null & n=0 & h=0 & s=0 or self::node3<_,p,q> * p::bt<np,hp,sp> * q::bt<nq,hq,sq> & n=1+np+nq & h=1+max(hp,hq) & s=1+min(sp,sq) inv n>=0 & h>=0 & s>=0;

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

/*@
bt<n,h> == self=null & n=0 & h=0
  or self::node3<_,p,q> * p::bt<np,hp> * q::bt<nq,hq> & n=1+np+nq & h=1+max(hp,hq)
  inv n>=0 & h>=0;

relation A(int a, int b, int c, int d).
*/
/*
Proving precondition in method __cast_void_pointer_to_node3__$void_star Failed.
  (may) cause: M_unmatched_rhs (infer_collect_hp_rel 3b)

Context of Verification Failure: c-examples/pure-data-struct/bt.c_29:10_29:33
*/
void insert(struct node3* x)
/*@
  infer [A,n,h]
  requires x::bt<n,h>
  ensures x::bt<m,k> & A(n,h,m,k);
*/
{
  struct node3 *a, *b;
  if (x->left == NULL){
    x->left = malloc(sizeof(node3));
    x->left->val = 0;
    x->left->left = NULL;
    x->left->right = NULL;
  }
  else {
    if (x->right == NULL) {
      x->right = malloc(sizeof(node3));
      x->right->val = 0;
      x->right->left = NULL;
      x->right->right = NULL;
    }
    else {
      if (a == b) insert(x->left);
      else insert(x->right);
    }
  }
}

