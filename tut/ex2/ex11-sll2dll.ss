data node{
  node prev;
  node next;
}

ll<> == self = null  or self::node< _ , q> * q::ll<>;
dll<p> == self = null or self::node< p , q> * q::dll<self>;   // p stores the prev node

HeapPred H1(node a, node@NI b).
PostPred G1(node a, node@NI b).

void sll2dll (node x, node p)
 infer[H1,G1] requires H1(x,p) ensures G1(x,p);
// requires x::ll<> ensures x::dll<p>;
{
  if (x!=null){
    x.prev=p;
    sll2dll(x.next,x);
  }
}
