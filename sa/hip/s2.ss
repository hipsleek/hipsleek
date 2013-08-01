/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


HeapPred H1(node a).
HeapPred G2(node a, node b).

node trav(node x)

     infer [H1,G2]
     requires H1(x)
     ensures G2(res,x);
  /* requires x::node<_,p> */
  /* ensures x::node<_,p> & res = null; */

{
  node t = x.next;
  if (t==null) return null;
  else {
    return null;
  }
}
