data node{
	node left;
	node right;
}

/* predicate for a tree */
tree<> == self = null
	or self::node<l,r> * l::tree<> * r::tree<>;

HeapPred H(node a).

int size (node x)
infer [H] requires H(x) ensures true;
//requires x::tree<> ensures true;
{
	if (x==null) return 0;
	else return size(x.left)+size(x.right)+1;
}
