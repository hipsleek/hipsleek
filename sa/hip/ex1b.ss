data node {
  int val;
  node next;
}

ll<> == self=null
	or self::node<_, q> * q::ll<>
	inv true;

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;

HeapPred H1(node a).
HeapPred H2(node a).


void foo1( node x)
 infer [H1,H2]
 requires H1(x)
 ensures H2(x); //'
 {
   if (x!=null) {
     x = x.next;
     foo1(x);
   }
 }

HeapPred H3(node a).
HeapPred H4(node a).

void foo2(node x)
 infer [H3,H4]
 requires H3(x)
 ensures  H4(x); //'
 {
   bool b;
   x = x.next;
   b = x!=null;
   if (b) {
     foo2(x);
   }
 }


