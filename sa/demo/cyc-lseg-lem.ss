data node {
  node next;
}.

HeapPred H(node x).
HeapPred G(node y).

pred ll<> == self=null
  or self::node<q>*q::ll<>.

pred ll2<> == self=null
  or self::node<q>*q::ll2<>
  or self::node<q>*q::ll2<>.

pred ls<p> == self=p
  or self::node<q>*q::ls<p>.


lemma self::ll<> <-> self::ll2<>.

lemma self::ll<> <-> self::ls<null>.
