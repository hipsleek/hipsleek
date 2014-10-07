data node {
	int ele;
	int height;
	node left;
	node right;
}

// m: number of elements, n: height
// bal: 0: balanced, 1: left is higher, 2: right is higher

avl<m, n, bal> == self = null & m = 0 & n = 0 & bal=0
	or self::node<_, n, p, q> * p::avl<m1, n1, b1> * q::avl<m2, n2, b2>
		& m = 1+m1+m2 & -1 <= n1-n2 <=1 & tmp=max(n1, n2) & n = tmp + 1 
		& bal=n1-n2
		// & (n1=n2 & bal=0 | n1>n2 & bal=1 | n1<n2 & bal=2)
	inv m >= 0 & n >= 0;// & 1>=bal>=-1;

/* function to return the height of an avl tree */
int height(node x)

	requires x::avl<m, n, b>
	ensures x::avl<m, n, b> & res = n;

//	requires x::node<a, n, l, r> 
//		or x=null
//	ensures x::node<a, n, l, r> & res=n 
//		or x=null & res=0;

{
	if (x == null)
		return 0;
	else
		return x.height;
}

int get_max(int a, int b) 
	requires true ensures res=a & a>=b or res=b & b>a;
{
	if (a>=b) return a;
	else return b;
}

node insert(node t, int x) 
  requires t::avl<tm, tn, b>
  ensures res::avl<tm+1, resn, resb> & t!=null & tm>0 & tn>0 & (tn=resn | resn=tn+1 & resb!=0)
		or res::avl<1,1,0> & tn=0 & tm=0 & t=null;
{
	node tmp = null;
	if (t==null) 
		return new node(x, 1, tmp, tmp);
	else if (x < t.ele) {		

		t.left = insert(t.left, x);

		if (height(t.left) - height(t.right) == 2) {
			if (height(t.left.left) > height(t.left.right)) { 
				// once we incorpate BST property into the tree, we should be able to
				// perform this test based on the values of the inserted element (x)
				// and t.left.val

				t = rotate_left_child(t);
			}
			else {
				t = double_left_child(t);
			}
		}
	}
	else {
		t.right = insert(t.right, x);
		if (height(t.right) - height(t.left) == 2) {
			if (height(t.right.right) > height(t.right.left)) {
				t = rotate_right_child(t);
			}
			else {
				t = double_right_child(t);
			}
		}
	}

	t.height = get_max(height(t.left), height(t.right)) + 1;

	// assert t'::avl<ntm,ntn,ntb> & (ntn=tn | ntn=tn+1 & ntb>0);

	return t;
}

/*
	Insertion to the right subtree of the left subtree of the root.
	Height of the right subtree has increased, meaning an=max(bn, cn)
	as the left subtree (of the root) itself is an AVL.
*/
node double_left_child(node k3) 
{
	k3.left = rotate_right_child(k3.left);
	node tmp = rotate_left_child(k3);
	return tmp;
}

node double_right_child(node k1)
{
	k1.right = rotate_left_child(k1.right);
	node tmp = rotate_right_child(k1);
	return tmp;
}

node rotate_left_child(node k2)
{
	node k1 = k2.left;
	k2.left = k1.right;
	k1.right = k2;
	k2.height = get_max(height(k2.left), height(k2.right)) + 1;
	k1.height = get_max(height(k1.left), k2.height) + 1;
	/*
		Note that if we use height(k2) instead, verification fails.
		The reason is k2 has to be folded for height(k2) and then
		information about the subtrees is lost.

		Sequence "unfold then fold" (i.e. start with a view, unfold, then fold)
		preserves information.

		Sequence "fold then unfold" loses information.
	*/
	return k1;
}

node rotate_right_child(node k1)
{
	node k2 = k1.right;
	k1.right = k2.left;
	k2.left = k1;
	k1.height = get_max( height(k1.left), height(k1.right) ) + 1;
	k2.height = get_max( height(k2.right), k1.height) + 1;
	return k2;
}
