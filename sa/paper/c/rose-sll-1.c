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

/*

 // BIND
(0)H1(t) --> t::tree&lt;val,children&gt;@M *
HP_951(children),
 // PRE_REC
(2;0)HP_951(children)&
children!=null |#| t::tree&lt;val,children&gt;@M --> H2(children,t@NI),
 // POST
(1;0)t::tree&lt;val,children&gt;@M * HP_951(children)&
children=null --> G1(t),
 // POST
(2;0)t::tree&lt;val,children&gt;@M * G2(children,t)&
children!=null --> G1(t)]


 // BIND
(0)H1(t) --> t::tree&lt;val,children&gt;@M *
HP_983(children),
 // PRE_REC
(2;0)t::tree&lt;val,children&gt;@M * HP_983(children)&
children!=null --> H2(children,t),
 // POST
(1;0)t::tree&lt;val,children&gt;@M * HP_983(children)&
children=null --> G1(t),
 // POST
(2;0)G2(children,t)&children!=null &
t!=null --> G1(t)]


[ // BIND
(2;0)H2(l,par)&l!=null --> HP_1032(child,par@NI) * HP_1035(par,l@NI) *
l::node&lt;child,next,parent&gt;@M * HP_1033(next,par@NI) *
HP_1034(parent,par@NI),
 // PRE_REC
(1;2;0)HP_1033(next,par@NI) * HP_1035(par,l@NI) * HP_1034(parent,par@NI)&
par=parent --> H2(next,par),
 // PRE_REC
(1;1;2;0)HP_1032(child,par@NI) --> H1(child),
 // POST
(1;0)H2(l,par)&
l=null --> G2(l,par),
 // POST
(1;1;1;2;0)l::node&lt;child,next,par&gt;@M *
G2(next,par) --> G2(l,par)]


 */
