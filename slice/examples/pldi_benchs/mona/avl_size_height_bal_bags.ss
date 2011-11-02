data node {
	int ele;
	int height;
	node left;
	node right;
}

// m: number of elements, n: height
// bal: 0: left is higher, 1: balanced, 2: right is higher

avl<m, n, bal, S> == self = null & m = 0 & n = 0 & S = {} & bal=1
  or self::node<v, n, p, q> * p::avl<m1, n1, _, S1> * q::avl<m2, n2, _, S2>
		& m = 1+m1+m2 & n=1+max(n1, n2) 
		& -1 <= n1-n2 <=1 & ($ bal)=n1-n2+1
		& S = union({v}, S1, S2)  &
		forall (x : (x notin S1 | x <= v)) & forall (y : (y notin S2 | y >= v))
  inv m >= 0 & n >= 0 & 0<=bal<=2;

/* function to return the height of an avl tree */
int height(node x)

	requires x::avl<m, n, b, S>
	ensures x::avl<m, n, b, S> & res = n;

{
	if (x == null)
		return 0;
	else {
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

  requires t::avl<tm, tn, b, S>
  ensures res::avl<tm+1, resn, resb, S1> & t!=null & tm>0 & tn>0 
  & (tn=resn | resn=tn+1 & resb!=1) & S1 = union(S, {v})
		or res::avl<1,1,1,{x}> & tn=0 & tm=0 & t=null;
// --eps needs --esi
{
	node tmp = null;
	if (t==null) 
      {
        //assume false;
		return new node(x, 1, tmp, tmp);
      }
	else { 
        if (x < t.ele) {		
		t.left = insert(t.left, x);

		if (height(t.left) - height(t.right) == 2) {
			if (height(t.left.left) > height(t.left.right)) { 
				// once we incorpate BST property into the tree, we should be able to
				// perform this test based on the values of the inserted element (x)
				// and t.left.val
              //assume false;
				t = rotate_left_child(t);
			}
			else {
              //assume false;
				t = double_left_child(t);
			}
            //dprint;
		}
        //else {assume false;}
	}
	else {
      //assume false;
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
}

/*
	Insertion to the right subtree of the left subtree of the root.
	Height of the right subtree has increased, meaning an=max(bn, cn)
	as the left subtree (of the root) itself is an AVL.
*/
node double_left_child(node k3) 
	requires k3::node<vk3, _, k1, d> * d::avl<dm, dn, _, Sd>
		* k1::node<vk1, _, a, k2> * a::avl<am, an, _, Sa> 
		* k2::node<vk2, _, b, c> * b::avl<bm, bn, _, Sb> * c::avl<cm, cn, _, Sc>
                & bn<=1+an & an<=1+bn // -1<=an-bn<=1
                & cn<=1+dn & dn<=1+cn // -1<=an-bn<=1
	ensures res::node<v,h,ss1,ss2> * ss1::avl<am+bm+1,h1,_, S1>
                * ss2::avl<cm+dm+1,h2,_, S2>
                & h=1+t & t=max(h1,h2) & h1=1+t1 & t1=max(an,bn) 
				& h2=1+t2 & t2=max(cn,dn)
				& union({v}, S1, S2) = union({vk1, vk2, vk3}, Sa, Sb, Sc, Sd);
{
    node t2 = k3.left;
	k3.left = rotate_right_child(t2);
    
	/*
        assert k3'::node<_,_,kl,kr> * kr::avl<kcm, kcn, _> * kl::node<_, _, kll, klr> * klr::avl<kbm, kbn, _>
			* kll::avl<kam, kan, bbb>; 
		assert k3'::node<_,_,kl,kr> * kr::avl<kcm, kcn, _> * kl::node<_, _, kll, klr> * klr::avl<kbm, kbn, _>
			* kll::avl<kam, kan, _>; 
    */
	node tmp = rotate_left_child(k3);
	return tmp;
}

node double_right_child(node k1)
	requires k1::node<vk1, _, a, k2> * a::avl<am, an, _, Sa>
			* k2::node<vk2, _, k3, d> * d::avl<dm, dn, _, Sd>
			* k3::node<vk3, _, b, c> * b::avl<bm, bn, _, Sb> * c::avl<cm, cn, _, Sc>
			& bn<=1+an & an<=1+bn // -1<=an-bn<=1
			& cn<=1+dn & dn<=1+cn // -1<=an-bn<=1
			& forall (x1 : (x1 notin Sa | x1 <= vk1))
			& vk1 <= vk2
			& vk3 <= vk2 & vk3 >= vk1
			& forall (x21 : (x21 notin Sb | x21 <= vk3)) & forall (x22 : (x22 notin Sb | x22 >= vk1))
			& forall (x31 : (x31 notin Sc | x31 >= vk3)) & forall (x32 : (x32 notin Sc | x32 <= vk2))
			& forall (x4 : (x4 notin Sd | x4 >= vk2))
	ensures res::node<v,h,ss1,ss3> * ss1::avl<am+bm+1,h1,_, S1>
			* ss3::avl<cm+dm+1,h2,_, S3>
			& h=1+t & t=max(h1,h2) & h1=1+t1 & t1=max(an,bn) 
			& h2=1+t2 & t2=max(cn,dn)
			& union({vk1, vk2, vk3}, Sa, Sb, Sc, Sd) = union({v}, S1, S3)
			& forall (x5 : (x5 notin S1 | x5 <= v))
			& forall (x6 : (x6 notin S3 | x6 >= v))
			& v = vk3 & (vk1 in S1) & (vk2 in S3);
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
	requires k2::node<vk2, _, l, r> * r::avl<cm, cn, _, Sr> * l::node<vl, _, ll, lr> 
		* ll::avl<am, an, _, Sll> * lr::avl<bm, bn, _, Slr>
		& forall (x1 : (x1 notin Sll | x1 <= vl)) 
		& forall (x2 : (x2 notin Slr | x2 >= vl & x2 <= vk2)) //& forall (x3 : (x3 notin Slr | x3 <= vk2))
		& vl <= vk2
		& forall (x4 : (x4 notin Sr | x4 >= vk2))
	ensures res::node<v,resn, resl, resr> * resl::avl<am, an, _, S1> * resr::node<vrr,resrn,resrl,resrr>
		* resrl::avl<bm,bn, _, S2> * resrr::avl<cm,cn,_,S3>
		& resrn=tmp1+1 & tmp1=max(cn, bn)
		& resn=tmp2+1 & tmp2=max(an, resrn)
		& union({vk2, vl}, Sr, Sll, Slr) = union({v, vrr}, S1, S2, S3)
		& forall (x5 : (x5 notin S1 | x5 <= v))
		& vrr >= v
		& forall (x6 : (x6 notin S2 | x6 <= vrr & x6 >= v))
		& forall (x7 : (x7 notin S3 | x7 >= vrr))
		& v = vl & vrr = vk2
		& Sll = S1 & Slr = S2 & Sr = S3;
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
	requires k1::node<vk1, _, l, r> * l::avl<am, an, _, Sl>
		* r::node<vr, _, rl, rr> * rl::avl<bm, bn, _, Srl> * rr::avl<cm, cn, _, Srr>
		& forall (x1 : (x1 notin Sl | x1 <= vk1)) 
		& vk1 <= vr
		& forall (x2 : (x2 notin Srl | x2 <= vr & x2 >= vk1))
		& forall (x3 : (x3 notin Srr | x3 >= vr)) 
	ensures res::node<v1, resn, resl, resr> * resl::node<v2, resln, resll, reslr> * resr::avl<cm, cn, _, S1>
		* resll::avl<am, an, _, S2> * reslr::avl<bm, bn, _, S3>
		& resln=tmp1+1 & tmp1=max(an, bn)
		& resn=tmp2+1 & tmp2=max(resln, cn)
		& union({vk1, vr}, Sl, Srl, Srr) = union({v1, v2}, S1, S2, S3)
		& forall (x4 : (x4 notin S1 | x4 >= v1))
		& v2 <= v1
		& forall (x5 : (x5 notin S2 | x5 <= v2))
		& forall (x6 : (x6 notin S3 | x6 <= v1 & x6 >= v2))
		& v1 = vr & v2 = vk1
		& Sl = S2 & Srl = S3 & Srr = S1;
/*
	requires k1::node<_, _, l, r> * l::avl<lm, ln, _>
		* r::node<_, _, rl, rr> * rl::avl<rlm, rln, _> * rr::avl<rrm, rrn, _>
		& -1<=rrn-rln & -1<=ln-rln<=1
	ensures res::node<_, resn, resl, resr> * resl::node<_, resln, resll, reslr> * resr::avl<resrm, resrn, _>
		* resll::avl<resllm, reslln, _> * reslr::avl<reslrm, reslrn, _>
		& reslln=ln & reslrn=rln & resrn=rrn
		& resln=tmp1+1 & tmp1=max(reslln, reslrn)
		& resn=tmp2+1 & tmp2=max(resln, resrn)
		& lm=resllm & rlm=reslrm & rrm=resrm;
*/
{
	node k2 = k1.right;
	k1.right = k2.left;
	k2.left = k1;
	k1.height = get_max( height(k1.left), height(k1.right) ) + 1;
	k2.height = get_max( height(k2.right), k1.height) + 1;
	return k2;
}
