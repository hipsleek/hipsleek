
template data node_tml {
  int val;
  node_tml next;
}

ll<> == self=null
	or self::node_tml<_, q> * q::ll<>
	inv true;

lseg<p> == self=p
  or self::node_tml<_, q> * q::lseg<p>
  inv true;
