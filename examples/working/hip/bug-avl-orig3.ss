data node {
	int ele;
	int height;
	node left;
	node right;
}

// m: number of elements, n: height
// bal: 0: left is higher, 1: balanced, 2: right is higher

avl<m, n, bal> == self = null & m = 0 & n = 0 & bal=1
	or self::node<_, n, p, q> * p::avl<m1, n1, _> * q::avl<m2, n2, _>
		& m = 1+m1+m2 & n = max(n1, n2) + 1 
		// -1 <= n1-n2 <=1 
		& n2+bal=n1+1 & n2<=n1+1 & n1 <= 1+n2
	inv m >= 0 & n >= 0 & 0<=bal<=2 
     & -2+(2*bal)<=n & 2<=(2*bal)+n  &  -1+bal<=m & 1<=(bal+m)     ;

       (** example below takes a long eps on loris-7
        time to run; I wonder if this is due to an older
        version of Omega; the reson is that my laptop seems
        to run faster.*)

node insert(node t, int x) 
  requires t::avl<tm, tn, b>
  ensures res::avl<tm+1, resn, resb> & t!=null & tm>0 & tn>0 & (tn=resn | resn=tn+1 & resb!=1)
		or res::avl<1,1,1> & tn=0 & tm=0 & t=null;
// --eps needs --esi
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

