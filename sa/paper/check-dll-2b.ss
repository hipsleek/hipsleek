    
data node {
    node prev; 
    node next; 
    }

HeapPred H1(node a,node@NI b).
PostPred G1(node a,node@NI b).

dll<prev> == 
  self=null or 
  self::node<prev,n>* n::dll<self>;

bool check_dll (node l, node prv)
  //requires l::dll<prv>@L ensures  res;
  infer [H1,G1] requires H1(l,prv) ensures G1(l,prv) & res;
{
	if (l==null) return true;
	else { 
               return check_dll(l.next,l) && (l.prev==prv);
             }
}

/*
# check-dll-2b.ss

Same as check-dll-2.ss

*/
