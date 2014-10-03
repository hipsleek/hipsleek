data node{
        node prev;
        node up;
        node next;
}

ll<> == self = null  or self::node< _ ,_, q> * q::ll<>;
/*
llD<D1,D2> == self = null  or self::node< p ,u, q> * q::llD<D1,D2> 
       & p in D1 & u in D2;
*/
//HeapPred H1(node a, node@NI b).
// seems critical to have @NI
//HeapPred G1(node a, node b).

HeapPred H1(node a).
// seems critical to have @NI
HeapPred G1(node a).

void id (node x)
  infer[H1,G1] requires H1(x) ensures G1(x);
  //requires x::ll<> ensures x::ll<>;
  //requires x::llD<D1,D2> ensures x::llD<D2,D1>; // fails
//  requires x::llD<D1,D2> ensures x::llD<D1,D2>; // succeed
{
        if (x!=null) 
        {
	     id(x.next); 
        }
}

/*
# id

*/
