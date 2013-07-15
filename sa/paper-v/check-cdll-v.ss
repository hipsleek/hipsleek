data node{
	node prev;
	node next;
}

cdll<prev, p> ==  self= p
  or self::node<prev,n>* n::cdll<self, p>;

HeapPred H1(node a, node b, node c).
  HeapPred G1(node a, node b, node c).

bool check_cdll (node l, node prv, node p)
  requires l::cdll<prv,p>@L ensures  res;
//  infer [H1,G1] requires H1(l,prv,p) ensures G1(l,prv,p) & res;
{
	if (/* l== prv && */ l== p) return true;
	else { bool r1 = check_cdll(l.next,l,p);
               bool e1 = (l.prev==prv);
               return e1 && r1;
             }
}
