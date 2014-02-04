data node {
  int val;
  node next;
}

cll<p> == self = p
	or self::node<_, r> * r::cll<p> & self != p  
	inv true;

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
