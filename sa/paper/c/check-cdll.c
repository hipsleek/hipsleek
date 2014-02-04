struct node{
  struct node* prev;
  struct node* next;
};

/*@
cdll<prev, p> ==  self= p
  or self::node<prev,n>* n::cdll<self, p> & self!=p;
*/

/*@
HeapPred H1(node a, node@NI b, node@NI c).
  HeapPred G1(node a, node@NI b, node@NI c).
*/

int check_cdll (struct node* l, struct node* prv, struct node* p)
//  requires l::cdll<prv,p>@L ensures  res=1;
//@  infer [H1,G1] requires H1(l,prv,p) ensures G1(l,prv,p) & res=1;
{
  if (/* l== prv && */ l== p) return 1;
  else { int r1 = check_cdll(l->next,l,p);
    //int e1 = (l->prev==prv);
    return (l->prev==prv) && r1;
  }
}
