data node {
	int ele;
	int height;
	node left;
	node right;
}

// m: number of elements, n: height
// bal: 0: balanced, 1: left is higher, -1: right is higher

avl<n, bal> == self = null & n = 0 & bal = 0 
	or self::node<_, n, p, q> * p::avl<n1, b1> * q::avl<n2, b2>
		& bal = n1-n2 & -1 <= bal <=1 & tmp=max(n1, n2) & n = tmp + 1 
	inv n >= 0 & -1 <= bal <= 1;

tree<m> == self = null & m = 0
	or self::node<_, _, p, q> * p::tree<m1> * q::tree<m2> & m = m1+m2+1
	inv m >= 0;

bst <sm, lg> == self = null & sm <= lg 
	or self::node<v, _, p, q> * p::bst<sm, pl> * q::bst<qs, lg> & pl <= v & qs >= v 
	inv sm <= lg;

all<m, n, bal, sm, lg> == self = null & m = 0 & n = 0 & bal = 0 & sm <= lg
	or self::node<v, n, p, q> * p::all<m1, n1, bal1, sm, pl> * q::all<m2, n2, bal2, qs, lg> 
	& m = 1+m1+m2 /*& bal = n1-n2 & -1 <= bal <= 1*/ /*& tmp = max(n1, n2) & n = tmp+1 */
	& pl <= v & qs >= v
	inv m >= 0 /*& n >= 0*/ /*& -1 <= bal <= 1*/ & sm <= lg;


/* function to return the height of an avl tree */
int height(node x)
	/*requires x::avl<n, b>
	ensures x::avl<n, b> & res = n;
	
	requires x::tree<m>
	ensures x::tree<m>;
	
	requires x::bst<sm, lg>
	ensures x::bst<sm, lg>;*/
	
	requires x::all<m, n, bal, sm, lg>
	ensures x::all<m, n, bal, sm, lg> & res = n;

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
  /*requires t::avl<tn, b>
  ensures res::avl<resn, resb> & t != null & tn > 0 & (tn = resn | resn = tn+1 & resb != 0)
		or res::avl<1,0> & tn = 0 & t = null;
  requires t::tree<m>	
  ensures res::tree<m+1>;
 
  requires t::bst<sm, lg>	
  ensures res::bst<mi, ma> & res != null & (mi=sm | mi=x) & (ma=lg | ma=x);//mi = min(sm, x) & ma = max(lg, x);	*/	

  requires t::all<m, n, bal, sm, lg>
  ensures res::all<m+1, resn, resb, mi, ma> 
	& t != null & n > 0 & (resn = n | resn = n+1 & resb != 0) & res != null & (mi=sm | mi=x) & (ma=lg | ma=x)
	or res::all<m+1, 1, 0, mi, ma> & n = 0 & t = null & res != null & (mi=sm | mi=x) & (ma=lg | ma=x);		
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
				if (t.left != null && t.left.right != null)
					t = double_left_child(t);
				else 
					assume false;
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
				if (t.right != null && t.right.left != null)
					t = double_right_child(t);
				else 
					assume false;
			}
		}
	}
	if(t != null) {
		t.height = get_max(height(t.left), height(t.right)) + 1;
	}
	else assume false;

	return t;
}

/*
	Insertion to the right subtree of the left subtree of the root.
	Height of the right subtree has increased, meaning an=max(bn, cn)
	as the left subtree (of the root) itself is an AVL.
*/
node double_left_child(node k3) 
	/*requires k3::node<_, _, k1, d> * d::avl<dn, _>
		* k1::node<_, _, a, k2> * a::avl<an, _> 
		* k2::node<_, _, b, c> * b::avl<bn, _> * c::avl<cn, _>
		& -1 <= bn-cn <= 1 & -1 <= cn-dn <= 1 & an = max(bn, cn) & an = dn
	ensures res::avl<resn, _> & resn = an+2;
	
	requires k3::node<_, _, k1, d> * d::tree<dm>
		* k1::node<_, _, a, k2> * a::tree<am> 
		* k2::node<_, _, b, c> * b::tree<bm> * c::tree<cm>
	ensures res::tree<resm> & resm = dm+am+bm+cm+3;
	
	requires k3::node<v1, _, k1, d> * d::bst<sm1, lg>
		* k1::node<v2, _, a, k2> * a::bst<sm, lg2> 
		* k2::node<v3, _, b, c> * b::bst<sm2, lg3> * c::bst<sm3, lg1>
		& sm1 >= v1 & lg1<= v1 & sm2 >= v2 & lg2 <= v2 & sm3 >= v3 & lg3 <= v3 
	ensures res::bst<sm, lg>;*/


	requires k3::node<v1, _, k1, d> * d::all<dm, dn, _,  sm1, lg>
		* k1::node<v2, _, a, k2> * a::all<am, an, _, sm, lg2> 
		* k2::node<v3, _, b, c> * b::all<bm, bn, _, sm2, lg3> * c::all<cm, cn, _, sm3, lg1>
		& sm1 >= v1 & lg1<= v1 & sm2 >= v2 & lg2 <= v2 & sm3 >= v3 & lg3 <= v3 
		& -1 <= bn-cn <= 1 & -1 <= cn-dn <= 1 & an = max(bn, cn) & an = dn
	ensures res::all<resm, resn, _, sm, lg> & resm = dm+am+bm+cm+3 & resn = an+2;

{
	k3.left = rotate_right_child(k3.left);
	node tmp;
	//assert k3'::avl<_, _>;
	//assert k3'::all<_, _, _, _, _>;
	tmp = rotate_left_child(k3);
	return tmp;
}

node double_right_child(node k1)
	/*requires k1::node<_, _, a, k2> * a::avl<an, _>
		* k2::node<_,_, k3, d> * d::avl<dn, _>
		* k3::node<_,_, b, c> * b::avl<bn, _> * c::avl<cn, _>
		& -1 <= bn-cn <= 1 & -1 <= an-bn <= 1 & -1 <= cn-dn <= 1 & dn = max(bn, cn) & an = dn 
	ensures res::avl<resn, _> & resn = dn+2;
	
	requires k1::node<_, _, a, k2> * a::tree<am>
		* k2::node<_,_, k3, d> * d::tree<dm>
		* k3::node<_,_, b, c> * b::tree<bm> * c::tree<cm>
	ensures res::tree<resm> & resm = am+bm+cm+dm+3;

	requires k1::node<v1, _, a, k2> * a::bst<sm, lg1>
		* k2::node<v2,_, k3, d> * d::bst<sm2, lg>
		* k3::node<v3,_, b, c> * b::bst<sm1, lg3> * c::bst<sm3, lg2>
		& sm1 >= v1 & lg1<= v1 & sm2 >= v2 & lg2 <= v2 & sm3 >= v3 & lg3 <= v3 
	ensures res::bst<sm, lg>;*/

	requires k1::node<v1, _, a, k2> * a::all<am, an, _,  sm, lg1>
		* k2::node<v2, _, k3, d> * d::all<dm, dn, _, sm2, lg> 
		* k3::node<v3, _, b, c> * b::all<bm, bn, _, sm1, lg3> * c::all<cm, cn, _, sm3, lg2>
		& sm1 >= v1 & lg1<= v1 & sm2 >= v2 & lg2 <= v2 & sm3 >= v3 & lg3 <= v3
		& -1<=bn-cn<=1 & -1<=an-bn<=1 & -1<=cn-dn<=1 & dn=max(bn, cn) & an=dn  
	ensures res::all<resm, resn, _, sm, lg> & resm = dm+am+bm+cm+3 & resn = dn+2;

{
	k1.right = rotate_left_child(k1.right);
	node tmp = rotate_right_child(k1);
	return tmp;
}

node rotate_left_child(node k2)
	/*requires k2::node<_, _, l, r> * r::avl<rn, _> * l::node<_, _, ll, lr> 
		* ll::avl<lln, _> * lr::avl<lrn, _>
		& -1 <= lln-lrn/*<=1*/ & -1 <= lrn-rn <= 1
	ensures res::node<_,resn, resl, resr> * resl::avl<resln, _> * resr::node<_,resrn,resrl,resrr>
		* resrl::avl<resrln, _> * resrr::avl<resrrn, _>
		& resln = lln & resrln = lrn & resrrn = rn
		& resrn = tmp1+1 & tmp1 = max(resrln, resrrn)
		& resn = tmp2+1 & tmp2 = max(resln, resrn);

	requires k2::node<_, _, l, r> * r::tree<rm> * l::node<_, _, ll, lr> 
		* ll::tree<llm> * lr::tree<lrm>
	ensures res::node<_,_, resl, resr> * resl::tree<reslm> * resr::node<_,_,resrl,resrr>
		* resrl::tree<resrlm> * resrr::tree<resrrm>
		& llm = reslm & lrm = resrlm & rm = resrrm;

	requires k2::node<v1, _, l, r> * r::bst<sm1, lg> * l::node<v2, _, ll, lr> 
		* ll::bst<sm, lg2> * lr::bst<sm2, lg1>
		& lg1 <= v1 & sm1 >= v1 
		& lg2 <= v2 & sm2 >= v2 
	ensures res::node<v3, _, resl, resr> * resl::bst<sm, lg3> * 
		resr::node<v4, _,resrl,resrr>
		* resrl::bst<sm3, lg4> * resrr::bst<sm4, lg>
		& lg3 <= v3 & sm3 >= v3 
		& lg4 <= v4 & sm4 >= v4;*/

	requires k2::node<v1, _, l, r> * r::all<rm, rn, _,  sm1, lg>
		* l::node<v2, _, ll, lr> * ll::all<llm, lln, _, sm, lg2> 
		* lr::all<lrm, lrn, _, sm2, lg1>
		& -1 <= lln-lrn & -1 <= lrn-rn <= 1
		& sm1 >= v1 & lg1<= v1 & sm2 >= v2 & lg2 <= v2 
	ensures res::node<v3, _, resl, resr> * resl::all<reslm, resln, _, sm, lg3> 
		* resr::node<v4, _, resrl, resrr> * resrl::all<resrlm, resrln, _, sm3, lg4> * resrr::all<resrrm, resrrn, _, sm4, lg>
		& lg3 <= v3 & sm3 >= v3 & lg4 <= v4 & sm4 >= v4
		& resln = lln & resrln = lrn & resrrn = rn
		& resrn = tmp1+1 & tmp1 = max(resrln, resrrn)
		& resn = tmp2+1 & tmp2 = max(resln, resrn)
		& llm = reslm & lrm = resrlm & rm = resrrm;

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
	/*requires k1::node<_, _, l, r> * l::avl<ln, _>
		* r::node<_, _, rl, rr> * rl::avl<rln, _> * rr::avl<rrn, _>
		& -1 <= rrn-rln & -1 <= ln-rln <= 1
	ensures res::node<_, resn, resl, resr> * resl::node<_, resln, resll, reslr> * resr::avl<resrn, _>
		* resll::avl<reslln, _> * reslr::avl<reslrn, _>
		& reslln = ln & reslrn = rln & resrn = rrn
		& resln = tmp1+1 & tmp1 = max(reslln, reslrn)
		& resn = tmp2+1 & tmp2 = max(resln, resrn);

	requires k1::node<_, _, l, r> * l::tree<lm>
		* r::node<_, _, rl, rr> * rl::tree<rlm> * rr::tree<rrm>
	ensures res::node<_, _, resl, resr> * resl::node<_, _, resll, reslr> * resr::tree<resrm>
		* resll::tree<resllm> * reslr::tree<reslrm>
		& lm = resllm & rlm = reslrm & rrm = resrm;

	requires k1::node<v1, _, l, r> * l::bst<sm, lg1> 
		* r::node<v2, _, rl, rr> * rl::bst<sm1, lg2> * rr::bst<sm2, lg>
		& lg1 <= v1 & sm1 >= v1
		& lg2 <= v2 & sm2 >= v2
	ensures res::node<v3, _, resl, resr> * resl::node<v4, _, resll, reslr> 
		* resr::bst<sm3, lg> * resll::bst<sm, lg4> * reslr::bst<sm4, lg3>
		& lg3 <= v3 & sm3 >= v3 
		& lg4 <= v4 & sm4 >= v4;*/

	requires k1::node<v1, _, l, r> * l::all<lm, ln, _,  sm, lg1>
		* r::node<v2, _, rl, rr> * rl::all<rlm, rln, _, sm1, lg2> 
		* rr::all<rrm, rrn, _, sm2, lg>
		& -1 <= rrn-rln & -1 <= ln-rln <= 1
		& sm1 >= v1 & lg1<= v1 & sm2 >= v2 & lg2 <= v2 
	ensures res::node<v3, _, resl, resr> * resr::all<resrm, resrn, _, sm3, lg> 
		* resl::node<v4, _,resll,reslr> * resll::all<resllm, reslln, _, sm, lg4> * reslr::all<reslrm, reslrn, _, sm4, lg3>
		& lg3 <= v3 & sm3 >= v3 & lg4 <= v4 & sm4 >= v4
		& reslln = ln & reslrn = rln & resrn = rrn
		& resln = tmp1+1 & tmp1 = max(reslln, reslrn)
		& resn = tmp2+1 & tmp2 = max(resln, resrn)
		& lm = resllm & rlm = reslrm & rrm = resrm;

{
	node k2 = k1.right;
	k1.right = k2.left;
	k2.left = k1;
	k1.height = get_max( height(k1.left), height(k1.right) ) + 1;
	k2.height = get_max( height(k2.right), k1.height) + 1;
	return k2;
}


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
