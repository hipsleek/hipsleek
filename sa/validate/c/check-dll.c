struct node {
  struct node* prev; 
  struct node* next;
};
/*@
HeapPred H1(node a,node@NI b).
PostPred G1(node a,node@NI b).
*/
/*@
dll<prev> == 
  self=null or 
  self::node<prev,n>* n::dll<self>;
*/
int check_dll (struct node* l, struct node* prv)
// requires l::dll<prv>@L ensures  res=1;
//@ infer [H1,G1] requires H1(l,prv) ensures G1(l,prv) & res=1;
{
  if (l==NULL) return 1;
  else { int r1 = check_dll(l->next,l);
    //bool e1 = (l->prev==prv);
    return (l->prev==prv) && r1;
  }
}

