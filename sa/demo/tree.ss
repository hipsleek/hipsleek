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

equivalence detection needs fixing

[ H(x_858) ::= 
 emp&x_858=null
 or (H(right_26_854)) * (H(left_26_853)) * 
    x_858::node<left_26_853,right_26_854>@M&true
 ,
 G(x_859) ::= x_859::tree@M[LHSCase]&true]
*/