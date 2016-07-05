data node2{
  node2 prev;
  node2 next;
}

ll<> == self = null  or self::node2< _ , q> * q::ll<>;
dll<p> == self = null or self::node2< p , q> * q::dll<self>;   // p stores the prev node

HeapPred H1(node2 a, node2@NI b).
PostPred G1(node2 a, node2@NI b).

void sll2dll (node2 x, node2 p)
 infer[H1,G1] requires H1(x,p) ensures G1(x,p);
// requires x::ll<> ensures x::dll<p>;
{
  if (x!=null){
    x.prev=p;
    sll2dll(x.next,x);
  }
}
