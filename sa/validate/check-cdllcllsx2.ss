    
data node2 {
  node1 dd;
  node2 prev; 
  node2 next; 
}

data node {
  int val;
  node next;
}

data node1 {
  node dd;
  node1 next;
}

/*
cll<p> == self = p
	or self::node<_, r> * r::cll<p> & self != p  
	inv true;
*/
HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

bool check_csll (node l, node p)
// requires l::cll<p>@L ensures  res;
  infer [H1,G1] requires H1(l,p) ensures G1(l,p) & res;
{
  if (l == p)
    return true;
  else {
    bool r1 = check_csll(l.next,p);
    return  r1;
  }
}

HeapPred H2(node1 a, node1 b).
HeapPred G2(node1 a, node1 b).

bool check_csll_outer1 (node1 l, node1 p)
// requires l::cll<p>@L ensures  res;
  infer [H2,G2] requires H2(l,p) ensures G2(l,p) & res;
{
  if (l == p)
    return true;
  else {
    bool r1 = check_csll_outer1(l.next,p);
    return  r1 && check_csll(l.dd, l.dd);
  }
}

HeapPred H3(node2 a,node2@NI b,node2@NI c).
  PostPred G3(node2 a,node2@NI b,node2@NI c).

bool check_cdll_outer2 (node2 l, node2 prv, node2 p)
//  requires l::cdll<prv,p>@L ensures  res;
  infer [H3,G3] requires H3(l,prv,p) ensures G3(l,prv,p) & res;
{
	if (l==p) return true;
	else { bool r1 = check_cdll_outer2(l.next,l,p);
               bool e1 = (l.prev==prv);
               return e1 && r1 && check_csll_outer1 (l.dd, l.dd);
             }
}
