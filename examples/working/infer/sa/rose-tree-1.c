struct tree {
  int val; 
  struct node* children;
};

struct node {
  struct tree* child; 
  struct node* next; 
  struct tree* parent;
};

/*@
HeapPred H1(tree a).
PostPred G1(tree a).
HeapPred H2(node a,tree@NI b).
PostPred G2(node a,tree b).
*/

/*@
treep<> == 
  self::tree<_,c>* c::sll<self> ;

sll<parent> == 
  self=null or 
  self::node<c,n,parent>*c::treep<>* n::sll<parent>;
*/

int check_tree (struct tree* t)
/*
requires t::treep<> //& t!=null 
  ensures res=1;
*/
/*@
  infer [H1,H2,G1,G2]
  requires H1(t) //t::treep<>@L //& t!=null 
  ensures G1(t) & res=1;
*/
{
   if (t->children==NULL) return 1;
   else return check_child(t->children,t);
}

int check_child (struct node* l, struct tree* par)
/*
 requires l::sll<par> 
  ensures  res=1;
 */
/*@
  infer [H1,H2,G2,G2]
  requires H2(l,par) //l::sll<par>@L 
  ensures  G2(l,par) & res=1;
*/
{
	if (l==NULL) return 1;
	else if (l->parent==par) return check_child(l->next, par)&& check_tree(l->child);
	else return 0;
}

