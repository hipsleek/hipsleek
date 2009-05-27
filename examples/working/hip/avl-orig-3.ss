data node {
	int ele;
	int height;
	node left;
	node right;
}

// m: number of elements, n: height
// bal: 0: left is higher, 1: balanced, 2: right is higher


avl<m, n, bal> == 
 case {
  self = null -> [] m = 0 & n = 0 & bal=1;
  self!=null -> [] self::node<_, n, p, q> * p::avl<m1, n1, _> * q::avl<m2, n2, _>
		& m = 1+m1+m2 & n=1+max(n1, n2) 
  & -1 <= n1-n2 <=1 & bal=n1-n2+1; }
		//& n2+bal=n1+1 & n2<=n1+1 & n1 <= 1+n2
		// & (n1=n2 & bal=0 | n1>n2 & bal=1 | n1<n2 & bal=2)
	inv m >= 0 & n >= 0 & 0<=bal<=2;
/*

avl<m, n, bal> == self = null & m = 0 & n = 0 & bal=1
        or self::node<_, n, p, q> * p::avl<m1, n1, _> * q::avl<m2, n2, _>
                & m = 1+m1+m2 & n=1+max(n1, n2)
                & -1 <= n1-n2 <=1 & bal=n1-n2+1
                //& n2+bal=n1+1 & n2<=n1+1 & n1 <= 1+n2
                // & (n1=n2 & bal=0 | n1>n2 & bal=1 | n1<n2 & bal=2)
        inv m >= 0 & n >= 0 & 0<=bal<=2;

*/

/*

Based on structured predicate :

Total verification time: 255.06 second(s)
        Time spent in main process: 13.07 second(s)
        Time spent in child processes: 241.99 second(s)
         Sat time: 275.259677172 sec
         Imp time: 11.2225613594 sec

 imply 10
 no imply 138
 imply >1 sec, 456


sat >1 sec :516
3.04522800446 7.89950323105 7.0339949131 1.80495905876 3.16403412819 8.07533288002 7.37428402901 1.57497406006 1.37358593941 6.99352192879 1.81029319763 7.3426759243 1.36193418503 6.08314299583 7.02461600304 1.09210395813 1.79975891113 6.48829102516 7.30293178558 1.288230896 1.36316084862 3.82582879066 7.44460105896 1.88352203369 3.96941900253 7.4924120903 1.09505915642 2.97087407112 2.68626999855 4.10851192474 7.40708398819 1.11822915077 3.13289213181 3.0006210804 4.13149499893 7.64918994904 1.428606987 2.41496706009 2.23565387726 1.86967396736 1.02176213264 1.01349902153 2.32081103325 1.90713500977 1.70996403694 5.26336812973 4.70966076851 10.0073130131 1.57378315926 1.36802101135 1.29405093193 4.73089790344 2.07656502724 5.13877415657 10.0072090626 10.0072250366 2.19413781166 1.00756812096 4.57667398453 

Based on flat predicate for avl



Total verification time: 135.73 second(s)
        Time spent in main process: 8.77 second(s)
        Time spent in child processes: 126.96 second(s)
         Sat time: 82.6930940151 sec
         Imp time: 52.234300375 sec

 imply 0
 no imply 2
 imply >1 sec, 344
2.27128410339 2.20199799538 3.02461600304 2.20724987984 2.11409902573 2.12129497528 2.03383898735 5.64433193207 4.52622795105 4.55458903313 2.08573293686 2.07478380203 1.91653490067 1.92086005211 

sat >1 sec :252
5.76265215874 1.72952890396 5.9522061348 1.22812008858 4.98275709152 5.79944896698 1.0203499794 1.72084999084 5.23928713799 5.99601387978 1.13989806175 1.22873187065 3.09696102142 3.20132112503 3.3189201355 3.30062294006 1.28384304047 1.65892791748 1.00214910507 1.68056511879 1.33293294907 1.94884204865 
chinwn@loris-7:~/cvs/sleekex/examples/working/hip$ 

 */

/* function to return the height of an avl tree */
int height(node x)
// slow when it is addedi - 72s for insert without
/*
        requires x=null
        ensures res=0;
        requires x::node<v,h,l,r>
        ensures x::node<v,h,l,r> & res=h;
*/
// fails if last case dropped though it seem redundant
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
  case { 
   t=null ->
     requires true
     ensures res::avl<1,1,1> ;
   t!=null ->
     requires t::avl<tm, tn, b> 
     ensures res::avl<tm+1, resn, resb> &  (tn=resn | resn=tn+1 & resb!=1);
  }
/* cannot be verified without case analysis
  requires t::avl<tm, tn, b>
  ensures res::avl<tm+1, resn, resb> & t!=null & tm>0 & tn>0 & (tn=resn | resn=tn+1 & resb!=1)
		or res::avl<1,1,1> & tn=0 & tm=0 & t=null;
*/
{
	node tmp = null;
	if (t==null) 
		return new node(x, 1, tmp, tmp);
	else if (x < t.ele) {		
                dprint;
                tmp = t.left;
		t.left = insert(tmp, x);

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
	ensures res::node<_,h,ss1,ss2> * ss1::avl<am+bm+1,h1,_>
                * ss2::avl<cm+dm+1,h2,_>
                & h=1+t & t=max(h1,h2) & h1=1+t1 & t1=max(an,bn) 
	        & h2=1+t2 & t2=max(cn,dn);
/*	requires k3::node<_, _, k1, d> * d::avl<dm, dn, _>
		* k1::node<_, _, a, k2> * a::avl<am, an, _> 
		* k2::node<_, _, b, c> * b::avl<bm, bn, _> * c::avl<cm, cn, _>
		& -1<=bn-cn<=1
		& -1<=cn-dn<=1
        	& an=max(bn,cn) & an=dn
	ensures res::avl<resm,resn, _> & resn=an+2 & resm=dm+am+bm+cm+3;
*/
{
        node t2 = k3.left;
	k3.left = rotate_right_child(t2);
        //dprint;
	/*
        assert k3'::node<_,_,kl,kr> * kr::avl<kcm, kcn, _> * kl::node<_, _, kll, klr> * klr::avl<kbm, kbn, _>
         * kll::avl<kam, kan, bbb>; 
	assert k3'::node<_,_,kl,kr> * kr::avl<kcm, kcn, _> * kl::node<_, _, kll, klr> * klr::avl<kbm, kbn, _>
         * kll::avl<kam, kan, _>; 
        */
	node tmp = rotate_left_child(k3);
	return tmp;
}
/*
	requires k2::node<_, _, l, r> * r::avl<cm, cn, _> * l::node<_, _, ll, lr> 
		* ll::avl<am, an, _> * lr::avl<bm, bn, _>
	ensures res::node<_,resn, resl, resr> * resl::avl<am, an, _> * resr::node<_,resrn,resrl,resrr>
*/

node double_right_child(node k1)
	requires k1::node<_, _, a, k2> * a::avl<am, an, _>
			* k2::node<_,_, k3, d> * d::avl<dm, dn, _>
			* k3::node<_,_, b, c> * b::avl<bm, bn, _> * c::avl<cm, cn, _>
                & bn<=1+an & an<=1+bn // -1<=an-bn<=1
                & cn<=1+dn & dn<=1+cn // -1<=an-bn<=1
	ensures res::node<_,h,ss1,ss3> * ss1::avl<am+bm+1,h1,_>
                * ss3::avl<cm+dm+1,h2,_>
                & h=1+t & t=max(h1,h2) & h1=1+t1 & t1=max(an,bn) 
	        & h2=1+t2 & t2=max(cn,dn);
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
	requires k2::node<_, _, l, r> * r::avl<cm, cn, _> * l::node<_, _, ll, lr> 
		* ll::avl<am, an, _> * lr::avl<bm, bn, _>
	ensures res::node<_,resn, resl, resr> * resl::avl<am, an, _> * resr::node<_,resrn,resrl,resrr>
		* resrl::avl<bm,bn, _> * resrr::avl<cm,cn,_>
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
	requires k1::node<_, _, l, r> * l::avl<am, an, _>
		* r::node<_, _, rl, rr> * rl::avl<bm, bn, _> * rr::avl<cm, cn, _>
	ensures res::node<_, resn, resl, resr> * resl::node<_, resln, resll, reslr> * resr::avl<cm, cn, _>
		* resll::avl<am, an, _> * reslr::avl<bm, bn, _>
		& resln=tmp1+1 & tmp1=max(an, bn)
		& resn=tmp2+1 & tmp2=max(resln, cn);
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
/*
node rotate_left_child_2(node k2)
	requires k2::node<_, _, l, r> * r::avl<rm, rn> * l::node<_, _, ll, lr> * 
			ll::avl<llm, lln> * lr::avl<lrm, lrn> & rn=lrn & lrn+1>=lln>=lrn
	ensures res::avl<rm+llm+lrm+2, rn+2>;
{
	node k1 = k2.left;
	k2.left = k1.right;
	k1.right = k2;
	k2.height = get_max( height(k2.left), height(k2.right) ) + 1;
	k1.height = get_max( height(k1.left), height(k2) ) + 1;
	return k1;
}*/
/*
void f(node x)
	requires x::avl<m, n> & m>0
	ensures x::node<_,_,_,_>;
{
	//assert n>0;
	//assert x::node<_,_,_,_>;
}

void g(node x)
	requires x::avl<m,n> & n>0
	ensures x::avl<m,n>;
{
	int h = height(x.left);
}

void h(node x)
	requires x::node<_,_,_,r> * r::node<_,_,_,_>
	ensures true;
{
	h(x);
	h(x);
}

node k()
	requires true
	ensures res::avl<1,1,0>;
{
	node tmp = new node(10,1,null,null);

	return tmp;
}

void g(node x)
	requires x::avl<m,n,b> & n=0
	ensures x::avl<m,n,b> & m=0;
{
	assert x=null;
}

node test(node t)
  requires t::node<_, _, k1, d> * d::avl<dm, dn, _>
		* k1::node<_, _, a, k2> * a::avl<am, an, _> 
		* k2::node<_, _, b, c> * b::avl<bm, bn, _> * c::avl<cm, cn, _>
		& -1<=bn-cn<=1
		& -1<=cn-dn<=1
		& an=max(bn,cn) & an=dn
  ensures 1<0;
{
	t = double_left_child(t);
	return t;
}
*/
