    
data node1 {
  node dd1;
  node dd2;
  node1 prev; 
  node1 next; 
}

data node {
  int val;
  node next;
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

HeapPred H2(node1 a,node1@NI b,node1@NI c).
  PostPred G2(node1 a,node1@NI b,node1@NI c).

bool check_cdll_out1 (node1 l, node1 prv, node1 p)
//  requires l::cdll<prv,p>@L ensures  res;
  infer [H2,G2] requires H2(l,prv,p) ensures G2(l,prv,p) & res;
{
	if (l==p) return true;
	else { bool r1 = check_cdll_out1(l.next,l,p);
               bool e1 = (l.prev==prv);
               return e1 && r1 && check_csll (l.dd1, l.dd1) && check_csll (l.dd2, l.dd2);
             }
}
