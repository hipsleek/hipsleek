data node {
	int ele;
	int height;
	node left;
	node right;
}

// m: number of elements, n: height
avl<m, n> == self = null & m = 0 & n = 0 
	or self::node<_, n, p, q> * p::avl<m1, n1> * q::avl<m2, n2> 
		& m = 1+m1+m2 & -1 <= n1-n2 <=1 & tmp=max(n1, n2) & n = tmp + 1 
	inv m >= 0 & n >= 0;

/* function to return the height of an avl tree */
int height(node x)
	requires x::avl<m, n>
	ensures x::avl<m, n> & res = n & m>=0 & n>=0;	
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
  requires t::avl<tm, tn>
  ensures res::avl<tm+1, resn> & tn<=resn<=tn+1;
{
	node tmp = null;
	if (t==null) return new node(x, 1, tmp, tmp);
	else if (x < t.ele) {
		t.left = insert(t.left, x);
		if (height(t.left) - height(t.right) == 2) {
			if (height(t.left.left) > height(t.left.right)) {
				t = rotate_left_child(t);	
			}
			else if (height(t.left.left) == height(t.left.right) - 1) {
				assert t::node<_,_,k1,d> * d::avl<dm, dn>
					* k1::node<_,_,a,k2> * a::avl<am,an> * k2::node<_,_,b,c>
					* b::avl<bm, bn> * c::avl<cm, cn>
					& an=dn & an=max(bn, cn) & -1<=bn-cn<=1;

				t = double_left_child(t);
			}
			else {
				assume false;
			}
		}
		else {
			assume false;
		}
	}
	else {
		assume false;
	}

	return t;
}

node rotate_left_child(node k2)
	requires k2::node<_, _, l, r> * r::avl<rm, rn> * l::node<_, _, ll, lr> * 
			ll::avl<llm, lln> * lr::avl<lrm, lrn> & rn=lrn & lrn+1>=lln>=lrn
	ensures res::node<_,resn, resl, resr> * resl::avl<reslm, resln> * resr::avl<resrm, resrn>
		& (resrn=resln+1 & lln=lrn | resrn=resln & lln=lrn+1) & resn=resrn+1 & resn=rn+2
		& reslm+resrm=rm+llm+lrm+1;
{
	node k1 = k2.left;
	k2.left = k1.right;
	k1.right = k2;
	k2.height = get_max( height(k2.left), height(k2.right) ) + 1;
	k1.height = get_max( height(k1.left), height(k2) ) + 1;
	return k1;
}


node rotate_right_child(node k1)
	requires k1::node<_, _, l, r> * l::avl<lm, ln>
			* r::node<_, _, rl, rr> * rl::avl<rlm, rln> * rr::avl<rrm, rrn>
			& ln=rln & rln+1>=rrn>=rln
	ensures res::node<_,resn, resl, resr> * resl::avl<reslm, resln> * resr::avl<resrm, resrn>
		& (resln=resrn+1 & rrn=rln | resln=resrn & rrn=rln+1) & resn=resln+1 & resn=ln+2
		& reslm+resrm=lm+rlm+rrm+1;
{
	node k2 = k1.right;
	k1.right = k2.left;
	k2.left = k1;
	k1.height = get_max( height(k1.left), height(k1.right) ) + 1;
	k2.height = get_max( height(k2.right), k1.height) + 1;
	return k2;
}


node double_left_child(node k3) 
	requires k3::node<_, _, k1, d> * d::avl<dm, dn>
			* k1::node<_, _, a, k2> * a::avl<am, an> * k2::node<_, _, b, c>
			* b::avl<bm, bn> * c::avl<cm, cn>
			& an=dn & an=max(bn, cn) & bn=cn // the last condition (bn=cn) is too strong
			//& an=dn & an=bn & bn<=cn<=bn+1
	ensures res::avl<resm,resn> & resn=an+2 & resm=dm+am+bm+cm+3;
{
	k3.left = rotate_right_child(k3.left);
	//assert k3::node<_,_,l,r> * r::avl<rm, rn> * l::node<_,_,ll,lr> * ll::avl<llm, lln> * lr::avl<lrm, lrn>
	//	& rn=lrn & lrn+1>=lln>=lrn;
	return rotate_left_child(k3);
}

/*
void f(node x)
	requires x::avl<m, n> & m>0
	ensures x::node<_,_,_,_>;
{
	//assert n>0;
	//assert x::node<_,_,_,_>;
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
*/
