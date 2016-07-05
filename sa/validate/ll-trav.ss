data node {
  int val;
  node next;
}

/*
ll<> == self=null
	or self::node<_, q> * q::ll<>
	inv true;

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;
*/
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
HP_RELDEFN HP_539:  HP_539(x')::  H(x')
HP_RELDEFN G:  G(x)::
         x::node<val_16_546,x'> * G(x') & x!=null
            or emp & x=null
HP_RELDEFN H:  H(x)::
                   emp&x=null
               or x::node<val_16_522',next_16_523'> * H(next_16_523')&true
 */
