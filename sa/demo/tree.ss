data node{
	node left;
	node right;
}

/* predicate for a tree */
tree<> == self = null
	or self::node<l,r> * l::tree<> * r::tree<>;

HeapPred H(node a).
HeapPred G(node a).

int size (node x)

//infer [H] requires H(x) ensures H(x);

// below works 
infer [H,G] requires H(x) ensures G(x);

//infer [H] requires H(x) ensures true;
//requires x::tree<> ensures x::tree<>;
{
	if (x==null) return 0;
	else return size(x.left)+size(x.right)+1;
}

/*
# tree.ss

infer [H,G] requires H(x) ensures G(x);

PROBLEM with spurious XPURE
---------------------------
[ H(x)&x!=null --> x::node<left_24_795,right_24_796>@M * 
  (HP_797(left_24_795)) * (HP_798(right_24_796))&true,
 HP_797(left_24_795)&true --> H(left_24_795)&true,
 HP_798(right_24_796)&true --> H(right_24_796)&true,
 H(x)& XPURE(H(x)) & x=null --> G(x)&true,
       ^^^^^^^^^^^
 x::node<left_24_795,right_24_796>@M * (G(left_24_795)) * (G(right_24_796))&
  true --> G(x)&true]

*/
