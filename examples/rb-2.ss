/* red black trees with parent pointer */

data node {
	int val;
	int color; /*  0 for black, 1 for red */
	node left;
	node right;
	node parent;
}

/* view for red-black trees with parent pointer */

rb2<bh> == self=null & bh=1
	or self::node<v, 0, l, r, null> * l::rb<self, _, bhl> * r::rb<self, _, bhr> & bhl=bhr & bh=1+bhl & l!=null & r!=null
	inv bh>=1;

rb<p, cl, bh> == self=null & bh = 1 & cl = 0
	or self::node<v, 1, l, r, p> * l::rb<self, 0, bhl> * r::rb<self, 0, bhr> & cl = 1 & bhl = bh & bhr = bh
	or self::node<v, 0, l, r, p> * l::rb<self, _, bhl> * r::rb<self, _, bhr> & cl = 0 & bhl = bhr & bh = 1 + bhl
	inv bh >= 1 & 0 <= cl <= 1;

treep<p> == self=null
	or self::node<_, _, l, r, p> * l::treep<self> * r::treep<self>;

node insert(node tree, node parent, int v) 
//	requires tree::rb<p, cl, bh>
//	ensures res::rb<_, _, _>;

	requires tree::rb2<bh>
	ensures res::rb2<bh>;

	requires tree::treep<parent>
	ensures res::treep<parent>;
{
	if (tree==null) {
		node new_node = new node(v, 1, null, null, parent);

		//insert_case1(new_node);

		return new_node;
	}
	else if (v < tree.val) {
		tree.left = insert(tree.left, tree, v); // insert to left subtree, with tree as parent
		return tree;
	}
	else {
		tree.right = insert(tree.right, tree, v); // insert to right subtree with tree as parent
		return tree;
	}
}

//void insert_case1(node new_node) {
	
//}
