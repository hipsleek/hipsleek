struct node2 {
  struct node1* dd;
  struct node2* prev; 
  struct node2* next; 
};

struct node {
  int val;
  struct node* next;
};

struct node1 {
  struct node* dd;
  struct node1* next;
};

/*@
cll<p> == self = p
	or self::node<_, r> * r::cll<p> & self != p  
	inv true;

csll<p> ==  self= p
  or self::node1<dd,n>* n::csll<p> * dd::cll<dd> & self != p;

cdll<prev, p> ==  self= p
  or self::node2<dd,prev,n>* n::cdll<self, p> * dd::csll<dd> & self != p ;
*/
/*@
HeapPred H1(node a, node b).
HeapPred G1(node a, node b).
*/
int check_csll (struct node* l, struct node* p)
// requires l::cll<p>@L ensures  res=1;
//@  infer [H1,G1] requires H1(l,p) ensures G1(l,p) & res=1;
{
  if (l == p)
    return 1;
  else {
    int r1 = check_csll(l->next,p);
    return  r1;
  }
}

/*@
HeapPred H2(node1 a, node1 b).
HeapPred G2(node1 a, node1 b).
*/
int check_csll_outer1 (struct node1* l, struct node1* p)
// requires l::csll<p>@L ensures  res=1;
//@  infer [H2,G2] requires H2(l,p) ensures G2(l,p) & res=1;
{
  if (l == p)
    return 1;
  else {
    int r1 = check_csll_outer1(l->next,p);
    return  r1 && check_csll(l->dd, l->dd);
  }
}
/*@
HeapPred H3(node2 a,node2@NI b,node2@NI c).
  PostPred G3(node2 a,node2@NI b,node2@NI c).
*/
int check_cdll_outer2 (struct node2* l, struct node2* prv, struct node2* p)
//  requires l::cdll<prv,p>@L ensures  res=1;
//@  infer [H3,G3] requires H3(l,prv,p) ensures G3(l,prv,p) & res=1;
{
  if (l==p) return 1;
  else { int r1 = check_cdll_outer2(l->next,l,p);
    //bool e1 = (l.prev==prv);
    return  (l->prev==prv) && r1 && check_csll_outer1(l->dd, l->dd);
  }
}
