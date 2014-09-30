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
cll0<p> == self = p
	or self::node1<d, r> * r::cll0<p> * d::cll<d> & self != p  
	inv true;
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
int check_csll_outer (struct node1* l, struct node1* p)
// requires l::cll0<p>@L ensures  res=1;
//@  infer [H2,G2] requires H2(l,p) ensures G2(l,p) & res=1;
{
  if (l == p)
    return 1;
  else {
    int r1 = check_csll_outer(l->next,p);
    return  r1 && check_csll(l->dd, l->dd);
  }
}
