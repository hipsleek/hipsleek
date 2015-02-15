/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

ll<> == self=null
	or self::node<_, q> * q::ll<>
	inv true;

HeapPred H1(node a).
HeapPred G2(node a, node b).

node trav(node x)

     infer [H1,G2]
     requires H1(x)
     ensures G2(res,x);


{
    bool b = rand();
    node t = x.next;
    if (b) return t;
	else {
      if (t==null) return x;
      else {
         t = trav(t);
         return x;
      }
    }
}

bool rand() 
  requires true
  ensures res or !res; 
