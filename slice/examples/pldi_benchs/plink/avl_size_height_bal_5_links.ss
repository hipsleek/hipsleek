data node {
	int ele;
	int height;
	node left;
	node right;
}

// m: number of elements, n: height
// bal: 0: left is higher, 1: balanced, 2: right is higher
// 20 ctrs
avl<m, n, bal> == self = null & m = 0 & n = 0 & bal=1
	or self::node<_, n, p, q> * p::avl<m1, n1, _> * q::avl<m2, n2, _>
		& m = 1+m1+m2 & n = max(n1, n2) + 1 
		// -1 <= n1-n2 <=1 
		& n2+($ bal)=n1+1 & n2<=n1+1 & n1 <= 1+n2
	inv m >= 0 & n >= 0 & 0<=bal<=2  &  ($ -2<=n-(2*(bal))) & 
  ($ 2<=(2*(bal))+n)  & ($ -1+(bal)<=m) & ($ 1<=((bal)+m)) & ($ (m >= n));

/* function to return the height of an avl tree */
int height(node x)
	requires x::avl<m, n, b>
	ensures x::avl<m, n, b> & res = n;

{
	//dprint;
	if (x == null) {
		//assume false;
		return 0;
	}
	else {
		//assume false;
		return x.height;
	}
}

int get_max(int a, int b) 
	requires true ensures res=a & a>=b or res=b & b>a;
{
	if (a>=b) return a;
	else return b;
}

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

/*
	Insertion to the right subtree of the left subtree of the root.
	Height of the right subtree has increased, meaning an=max(bn, cn)
	as the left subtree (of the root) itself is an AVL.
*/
node double_left_child(node k3) 
	requires k3::node<_, _, k1, d> * d::avl<dm, dn, _>
		* k1::node<_, _, a, k2> * a::avl<am, an, _> 
		* k2::node<_, _, b, c> * b::avl<bm, bn, _> * c::avl<cm, cn, _>
                & bn<=1+an & an<=1+bn // -1<=an-bn<=1
                & cn<=1+dn & dn<=1+cn // -1<=an-bn<=1
	ensures res::node<_,h,ss1,ss2> * ss1::avl<am+bm+1,h1,bb1>
                * ss2::avl<cm+dm+1,h2,bb2>
                & h=1+t & t=max(h1,h2) & h1=1+t1 & t1=max(an,bn) 
	        & h2=1+t2 & t2=max(cn,dn);
{
        node t2 = k3.left;
	k3.left = rotate_right_child(t2);
	node tmp = rotate_left_child(k3);
	return tmp;
}

node double_right_child(node k1)
	requires k1::node<_, _, a, k2> * a::avl<am, an, _>
			* k2::node<_,_, k3, d> * d::avl<dm, dn, _>
			* k3::node<_,_, b, c> * b::avl<bm, bn, _> * c::avl<cm, cn, _>
                & bn<=1+an & an<=1+bn // -1<=an-bn<=1
                & cn<=1+dn & dn<=1+cn // -1<=an-bn<=1
	ensures res::node<_,h,ss1,ss3> * ss1::avl<am+bm+1,h1,bb1>
                * ss3::avl<cm+dm+1,h2,bb2>
                & h=1+t & t=max(h1,h2) & h1=1+t1 & t1=max(an,bn) 
	        & h2=1+t2 & t2=max(cn,dn);
{
	k1.right = rotate_left_child(k1.right);
	node tmp = rotate_right_child(k1);
	return tmp;
}

node rotate_left_child(node k2)
	requires k2::node<_, _, l, r> * r::avl<cm, cn, ba3> * l::node<_, _, ll, lr> 
		* ll::avl<am, an, ba1> * lr::avl<bm, bn, ba2>
	ensures res::node<_,resn, resl, resr> * resl::avl<am, an, ba1> * resr::node<_,resrn,resrl,resrr>
		* resrl::avl<bm,bn, ba2> * resrr::avl<cm,cn,ba3>
		& resrn=tmp1+1 & tmp1=max(cn, bn)
		& resn=tmp2+1 & tmp2=max(an, resrn);
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
	requires k1::node<_, _, l, r> * l::avl<am, an, ba1>
		* r::node<_, _, rl, rr> * rl::avl<bm, bn, ba2> * rr::avl<cm, cn, ba3>
	ensures res::node<_, resn, resl, resr> * resl::node<_, resln, resll, reslr> * resr::avl<cm, cn, ba3>
		* resll::avl<am, an, ba1> * reslr::avl<bm, bn, ba2>
		& resln=tmp1+1 & tmp1=max(an, bn)
		& resn=tmp2+1 & tmp2=max(resln, cn);
{
	node k2 = k1.right;
	k1.right = k2.left;
	k2.left = k1;
	k1.height = get_max( height(k1.left), height(k1.right) ) + 1;
	k2.height = get_max( height(k2.right), k1.height) + 1;
	return k2;
}