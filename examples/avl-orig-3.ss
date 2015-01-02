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
		& (n1=n2 & bal=0 | n1>n2 & bal=1 | n1<n2 & bal=2)
	inv m >= 0 & n >= 0;

/* function to return the height of an avl tree */
int height(node x)
	requires x::avl<m, n, b>
	ensures x::avl<m, n, b> & res = n;
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
  ensures res::avl<tm+1, resn, resb> & t!=null & tm>0 & tn>0 & (tn=resn | resn=tn+1 & resb>0)
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
	requires k3::node<_, _, k1, d> * d::avl<dm, dn, _>
		* k1::node<_, _, a, k2> * a::avl<am, an, _> 
		* k2::node<_, _, b, c> * b::avl<bm, bn, _> * c::avl<cm, cn, _>
		& -1<=bn-cn<=1
		& -1<=cn-dn<=1
		& an=max(bn,cn) & an=dn
	ensures res::avl<resm,resn, _> & resn=an+2 & resm=dm+am+bm+cm+3;
{
	k3.left = rotate_right_child(k3.left);
	node tmp = rotate_left_child(k3);
	return tmp;
}

node double_right_child(node k1)
	requires k1::node<_, _, a, k2> * a::avl<am, an, _>
			* k2::node<_,_, k3, d> * d::avl<dm, dn, _>
			* k3::node<_,_, b, c> * b::avl<bm, bn, _> * c::avl<cm, cn, _>
			& -1<=bn-cn<=1
			& -1<=an-bn<=1
			& -1<=cn-dn<=1
			& dn=max(bn, cn) & an=dn
	ensures res::avl<resm, resn, _>
			& resn=dn+2 & resm=am+bm+cm+dm+3;
{
	k1.right = rotate_left_child(k1.right);

	/*
	assert k1'::node<_,_,l,r> * l::avl<lm, ln, _> 
			* r::node<_,_,rl,rr> * rl::avl<rlm,rln, _> * rr::avl<rrm, rrn, _>
			& -1<=ln-rln<=1;
	*/

	node tmp = rotate_right_child(k1);
	return tmp;
}

node rotate_left_child(node k2)
	requires k2::node<_, _, l, r> * r::avl<rm, rn, _> * l::node<_, _, ll, lr> 
		* ll::avl<llm, lln, _> * lr::avl<lrm, lrn, _>
		& -1<=lln-lrn/*<=1*/ & -1<=lrn-rn<=1
	ensures res::node<_,resn, resl, resr> * resl::avl<reslm, resln, _> * resr::node<_,resrn,resrl,resrr>
		* resrl::avl<resrlm,resrln, _> * resrr::avl<resrrm,resrrn, _>
		& resln=lln & resrln=lrn & resrrn=rn
		& resrn=tmp1+1 & tmp1=max(resrln, resrrn)
		& resn=tmp2+1 & tmp2=max(resln, resrn)
		& llm=reslm & lrm=resrlm & rm=resrrm;
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
	requires k1::node<_, _, l, r> * l::avl<lm, ln, _>
		* r::node<_, _, rl, rr> * rl::avl<rlm, rln, _> * rr::avl<rrm, rrn, _>
		/*& -1<=rln-rrn<=1*/ & -1<=ln-rln<=1
	ensures res::node<_, resn, resl, resr> * resl::node<_, resln, resll, reslr> * resr::avl<resrm, resrn, _>
		* resll::avl<resllm, reslln, _> * reslr::avl<reslrm, reslrn, _>
		& reslln=ln & reslrn=rln & resrn=rrn
		& resln=tmp1+1 & tmp1=max(reslln, reslrn)
		& resn=tmp2+1 & tmp2=max(resln, resrn)
		& lm=resllm & rlm=reslrm & rrm=resrm;
{
	node k2 = k1.right;
	k1.right = k2.left;
	k2.left = k1;
	k1.height = get_max( height(k1.left), height(k1.right) ) + 1;
	k2.height = get_max( height(k2.right), k1.height) + 1;
	return k2;
}

bst<n,sm,lg> == self = null & n=0 & sm <=lg 
	or self::node<v,_,l,r> * l::bst<n1,sm,ll> * r::bst<n2,rs,lg> & ll<=v & v<=rs & n =1+ n1+n2
	inv sm <= lg & n>=0;

node remove_min_2(node x)
	requires x::bst<n,s,b> & x!= null
	ensures  x::bst<n-1,s1,b>;
{
	if (x.left != null)
	{
		node tmp;
		if (x.left.left == null)
		{
			tmp = x.left.right;
			x.left = tmp;
			return x;
		}
		else return remove_min_2(x.left);
	}
	else
	{
		node tmp = x.right;
		return tmp; 
	}
}
node remove_min_3(node x)
	requires x::bst<n,s,b> & x!= null
	ensures res::bst<n-1,s1,b> & s1>=s;
{
	if (x.left == null)
		return x.right;
	else 
	{
		node tmp = remove_min_3(x.left);
		x.left = tmp;
		return x;
	}
}
int remove_min(ref node x)
	requires x::bst<n,s,b> & x!= null
	ensures x'::bst<n-1,s1,b> & s<=res <=s1;
{
	if (x.left != null)
	{
		if (x.left.left == null)
		{
			int val = x.left.ele;
			node tmp1 = x.left.right;
			x.left=tmp1;
			return val;
		}
			else
			{
				int tmp2;
				bind x to (_,_,xleft,_) in{
					tmp2 = remove_min(xleft);
				}
				return tmp2;
			}

	}
	else
		{
			int val = x.ele;
			x = x.right;
			return val;
		}
}
void deleteBST(ref node x,int a)
//	requires x::bst<sm,lg>
//	ensures x'::bst<s,l> & sm<=s & l<=lg;
{
	int tmp;
	if (x!= null)
	{
		bind x to (xval,_,xleft,xright) in
		{
			if (xval ==a)
			{
				if (xright == null)
					x = xleft;
				else
				{
					tmp = remove_min(xright);
					xval	 = tmp;
				}
			}
			else
			{
				if (xval <a)
					deleteBST(xright,a);
				else deleteBST(xleft,a);
			}
		}
	}
}
/*node buildBST(node x)
	requires x::avl<m,n,b> & x!= null
	ensures res::bst<_,_>;
{
	if (x.left != null)
		x.left = buildBST(x.left);
	else if (x.right != null)
		x.right = buildBST(x.right);
	return x;
} */
void rebalanceBST(ref node x)
{
	int leftH = height(x);
	int rightH = height(x);	
	if (leftH - rightH ==2)
	{
		if (height(x.left.left)>height(x.left.right))
			x = rotate_left_child(x);
		else x= double_left_child(x);
	}
	else if (leftH-rightH==-2)
	{
		if (height(x.right.right)> height(x.right.left))
			x = rotate_right_child(x);
		else x= double_right_child(x);
	}

}
 void delete(ref node x,int a)
	requires x::avl<m,n,b> & x!= null
	ensures x'::avl<m-1,n1,b1> & ( n1=n|n1=n-1);
{
	deleteBST(x,a);
	rebalanceBST(x);

}
void test()
	requires true
	ensures true;
{
	node left = new node(1,1,null,null);
	if (left !=null)
	{
		node tmp = left.left;
		assert tmp' = null;
	}
	node right = new node(3,1,null,null);
	node root = new node(2,2,left,right);
	assert root' != null;
//	deleteBST(root,1);//delete left node
//	deleteBST(root,3);//delete right node
//	deleteBST(root,2);//delete root node
//	remove_min(root);//delete left node
	assert root' != null;
	if (root != null)
	{
		node tmp = root.left;
		assert tmp' != null;
		if (root.left != null)
		{
			node tmp2 = root.left.left;
			assert tmp2' =null;
		}
	}
	assert root'::bst<n,sm,lg> & n=3;
	assert root'::bst<m,sm,lg> & m=n-1; 
	node root1 = remove_min_3(root);
	assert root1'::bst<n,sm,lg> & n=2;
	//assert root1'::bst<n-1,sm,lg>;
/*	assert root' != null;
	if (root != null){
		if (root.left != null)
		{
			node tmp3 = root.left;
			assert tmp3' = null;
		}
	}*/

}

