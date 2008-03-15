data node {
	int element;
	node left;
	node right;
}

data treeNode {
	node root;
	node nullNode;
}

bst<rval, sm, lg, nullnode> == self = nullnode & sm <= rval <= lg
	or self::node<rval, l, r> * l::bst<lval, sm, llg, nullnode> * r::bst<rvl, rsm, lg, nullnode>
	& sm <= llg <= rval <= rsm <= lg
	inv sm <= rval <= lg;

splayTree<rval, sm, lg, nullnode> == self::treeNode<r, nullnode> * nullnode::node<_,_,_> * r::bst<rval, sm, lg, nullnode>;

/**
 * Rotate binary tree node with left child.
 */

node rotateWithLeftChild( node k2 ) {
	node k1 = k2.left;
	k2.left = k1.right;
	k1.right = k2;
	return k1;
}

/**
 * Rotate binary tree node with right child.
 */
node rotateWithRightChild( node k1 ) {
	node k2 = k1.right;
	k1.right = k2.left;
	k2.left = k1;
	return k2;
}



/**
 * Internal method to perform a top-down splay.
 * The last accessed node becomes the new root.
 * @param x the target item to splay around.
 * @param t the root of the subtree to splay.
 * @return the subtree after the splay.
 */
node splay_helper(int x, node t, node leftTreeMax, node rightTreeMin, node nullNode) 
	requires t::bst<tval, tsm, tlg, nullNode> * nullNode::node<x,null,null> * leftTreeMax::node<_,nullNode,nullNode>
				& rightTreeMin = leftTreeMax
		or t::bst<tval, tsm, tlg, nullNode> * nullNode::node<x,null,null> * leftTreeMax

	ensures res::node<rv, rl, rr> * rl::bst<rlv, rlsm, rllg, nullNode> * rr::bst<rrv, rrsm, rrlg, nullNode>
			& rllg <= x <= rrsm;
{

	if (x < t.element) {
		if (x < t.left.element)
			t = rotateWithLeftChild(t);

		if (t.left != nullNode) {
			// Link Right
			rightTreeMin.left = t;
			rightTreeMin = t;
			t = t.left;
			
			splay_helper(x, t, header, nullNode);
		}
	}
	else if (x > t.element) {
		if( x.compareTo( t.right.element ) > 0 )
			t = rotateWithRightChild( t );

		if (t.right != nullNode) {
			// Link Left
			leftTreeMax.right = t;
			leftTreeMax = t;
			t = t.right;

			splay_helper(x, t, header, nullNode);
		}
	}

	leftTreeMax.right = t.left;
	rightTreeMin.left = t.right;
	t.left = header.right;
	t.right = header.left;
	return t;
}


/*

tree_lefthole<lm> == self=lm
or self::node<..> * l::tree_lefthole<lm> * r::tree<>

tree<> == ex y. root::tree_lefthole<y> * y::node<..>

--------------------------------

tree_two_holes<lm, rm> == self=null
	or self::node<_, lm, rm>
	or ex x,y. self::node<_, l, r> * l::tree_two_holes<lm, x> * r::tree_two_holes<y, rm> 
			* x::node<_, null, null> * y::node<_, null, null>

tree_left_hole<lm> == ex y. self::tree_two_holes<lm, y> * y::node<_,null,null>

tree_right_hole<rm> == ex y. self::tree_two_holes<y, rm> * y::node<_,null,null>

tree<> == self=null
	or ex x, y. self::tree_two_holes<x, y> * x::node<_, null, null> * y::node<_, null, null>

unfold tree_two_holes several times:

tree_left_hole<lm>

==> ex y. self::tree_two_holes<_, lm, y> * y::node<_,null,null>
==> ex y, y1, y2, l, r. self::node<_, l, r> * l::tree_two_holes<lm, y1> * r::tree_two_holes<y2, rm> 
			* y1::node<_, null, null> * y2::node<_, null, null>


unfold l::tree_two_holes<lm, y1> 
==> ex x, y. l::node<_, ll, lr> * ll::tree_two_holes<lm, x> * lr::tree_two_holes<y, y1> * y::node<_,null,null>


look at tree_left_hole<lm>: tree_two_holes can be empty, hence y::node<_,null,null>
can be unreachable... Doesn't really affect soundness, but integrity of definition
is affected. How do we rephrase it???

*/
