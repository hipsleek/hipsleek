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
  /* requires htrue&true */
  /* ensures res=x; */

{
  if (x==null) return x;
  else {
    return x;
  }
}
