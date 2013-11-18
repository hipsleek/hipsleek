data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<> == self = null
	or self::node<_, q> * q::ll<>
  inv true;

HeapPred H1(node a, int v).
  HeapPred G1(node a, int v).
node insert(node x, int v)
  /* requires x::node<_,p> * p::ll<> */
  /* ensures x::node<_,p1> * p1::ll<>; */
  infer[H1,G1]
  requires H1(x, v)
     ensures G1(x, v);

{
        node tmp_null = null;
        node xn;

   if (v <= x.val) {
     return new node(v, x);
   }
   else {
     // assume false;
     if (x.next != null)
       {
         xn = insert(x.next, v);
         x.next = xn;
         return x;
       }
     else
       {
         x.next = new node(v, tmp_null);
         return x;
       }
   }
}
