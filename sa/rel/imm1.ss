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

HeapPred H(node a).
HeapPred H1(node a).
HeapPred G(node a, node b).

void foo( node x)
 infer [H,H1]
 requires H(x)
 ensures H1(x); //'
 {
   if (x!=null) {
     x = x.next;
     foo(x);
   }
 }

/*
expected:

 */
