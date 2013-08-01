data node_l1 {
  int val;
  node_l1 next;
}

data node_l2 {
  node_l1 val;
  node_l2 next;
}


ll1<> == self=null
	or self::node_l1<_, q> * q::ll1<>
	inv true;

ll2<> == self=null
  or self::node_l2<v, q> * v::ll1<> * q::ll2<>
	inv true;

HeapPred H1(node_l1 a).
HeapPred H2(node_l1 a).
HeapPred H3(node_l2 a).
HeapPred H4(node_l2 a).

void seach_inner( node_l1 x)
 infer [H1,H2]
 requires H1(x)
 ensures H2(x); //'
 {
   if (x!=null) {
     x = x.next;
     seach_inner(x);
   }
 }

void seach_outer( node_l2 x)
 infer [H3,H4]
 requires H3(x)
 ensures H4(x); //'
 {
   if (x!=null) {
     seach_inner(x.val);
     x = x.next;
     seach_outer(x);
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
