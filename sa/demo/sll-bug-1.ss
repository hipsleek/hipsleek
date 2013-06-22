data node{
        int val;
        node prev;
        node next;
}.


ll<> == self = null  or self::node<_, _ , q> * q::ll<>;
dll<p> == self = null or self::node<_, p , q> * q::dll<self>;   // p stores the prev node

HeapPred H1(node a, node b).
HeapPred H2(node a, node@NI b).


infer [H1,H2] x::node<_,q>*H2(q,x) |- H1(q,x).
print residue.

