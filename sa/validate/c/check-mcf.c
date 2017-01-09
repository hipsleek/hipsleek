struct tree {
  int val; 
  struct node* children;
};

struct node {
  struct tree* child; 
  struct node* prev; 
  struct node* next; 
  struct tree* parent;
};

/*@
treep<> == 
  self::tree<_,c>* c::dll<self,null> ;

dll<parent, prev> == 
  self=null or 
  self::node<c,prev,n,parent>*c::treep<>* n::dll<parent,self>;
*/
  //self=null or
/*@
HeapPred H1(tree a).
PostPred G1(tree a).
HeapPred H2(node a,node@NI c,tree@NI b).
PostPred G2(node a,node@NI c,tree@NI b).
*/

int check_tree (struct tree* t)
 // requires t::treep<>@L ensures res=1;
//@ infer [H1,G1,H2,G2] requires H1(t) ensures G1(t) & res=1;
{
  if (t->children==NULL) return 1;
   else return check_child(t->children,NULL,t);
    //check_child(t.children,t,t); // (node * tree * tree)
}

int check_child (struct node* l, struct node* prv, struct tree* par)
// requires l::dll<par, prv>@L ensures  res=1;
//@  infer [H1,G1,H2,G2] requires H2(l,prv,par) ensures G2(l,prv,par) & res=1;
{
  if (l==NULL) return 1;
  else if (l->parent==par && l->prev==prv) 
    return check_child(l->next,l, par)&& check_tree(l->child);
  else return 0;
}

