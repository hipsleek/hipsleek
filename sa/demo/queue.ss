data node {
  int val;
  node next;
}.

pred ll<> == self=null
	or self::node<_, q> * q::ll<>
	inv true.

pred lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true.


lemma "V1" self::lseg<null> <-> self::ll<>.

checkentail x::ll<> |- x::lseg<null>.
