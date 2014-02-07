// --eps for pred-en-equiv

struct node1 {
 struct node* dd1;
  struct node* dd2;
   struct node* dd3;
    struct node* dd4;
   struct node* dd5;
  struct node1* prev; 
  struct node1* next; 
};

struct node {
  int val;
  struct node* next;
};

/*@
cll<p> == self = p
	or self::node<_, r> * r::cll<p> & self != p  
	inv true;

cdll<prev, p> ==  self= p
  or self::node1<dd1,dd2,dd3,dd4,dd5,prev,n>* n::cdll<self, p> * dd1::cll<dd1>
  *dd2::cll<dd2> * dd3::cll<dd3> * dd4::cll<dd4> * dd5::cll<dd5> & self!= p;
*/
/*@
HeapPred H1(node a, node b).
HeapPred G1(node a, node b).
*/

int check_csll (struct node* l, struct node* p)
// requires l::cll<p> ensures l::cll<p> & res=1;
//@  infer [H1,G1] requires H1(l,p) ensures G1(l,p) & res=1;
{
  if (l == p)
    return 1;
  else {
    int r1 = check_csll(l->next,p);
    return r1;
  }
}

/*@
HeapPred H2(node1 a,node1@NI b,node1@NI c).
  PostPred G2(node1 a,node1@NI b,node1@NI c).
*/

int check_cdll_out1 (struct node1* l, struct node1* prv, struct node1* p)
//  requires l::cdll<prv,p> ensures l::cdll<prv,p> &  res=1;
//@  infer [H2,G2] requires H2(l,prv,p) ensures G2(l,prv,p) & res=1;
{
  if (l==p) return 1;
  else {
    int r1 = check_cdll_out1(l->next,l,p);
    //int e1 = (l->prev==prv);
    return r1 && (l->prev==prv) && check_csll (l->dd1, l->dd1) && check_csll(l->dd2, l->dd2)
      && check_csll(l->dd3, l->dd3)
      && check_csll (l->dd4, l->dd4) && check_csll (l->dd5, l->dd5)  ;
  }
}
