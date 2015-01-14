struct node {
  int val;
  struct node* next;
};

/*@
cll<p> == self = p
	or self::node<_, r> * r::cll<p> & self != p  
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
