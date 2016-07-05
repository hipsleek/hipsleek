/* tree with parent pointer */

data node {
	int val;
	node left;
	node right;
	node parent;
}

treep<s, p> == self = null & s = 0
	or self::node<_, l, r, p> * l::treep<s1, self> * r::treep<s2, self> & s = s1 + s2 + 1
	inv s >= 0;

/* tree with parent pointer and a hole */
/* parameters: size, dangling parent pointer, dangling left/right pointer, 
	pointer to the node having the dangling left/right */
thole<s, p, hole, last> == self = hole & p = last & s = 0
	or self::node<_, l, r, p> * l::thole<s1, self, hole, last> * r::treep<s2, self> & s = s1 + s2 + 1
	or self::node<_, l, r, p> * l::treep<s1, self> * r::thole<s2, self, hole, last> & s = s1 + s2 + 1
	inv s >= 0;

node down(node x)
	requires x::treep<s, p> & x != null
	ensures x::thole<s1, p, res, l> * res::treep<s2, l> & s = s1 + s2;
{
	if (x.left == null) {
		return x;
	}
	else {
		node tmp = down(x.left);
dprint aa_ps;
		return tmp;
	}
}

//lemma self::thole<s1, p, cur, last> * cur::treep<s2, last> & self != cur & cur != null
//	<-> self::thole<s3, p, last, last1> * last::treep<s4, last1> & s1 + s2 = s3 + s4;

void lemma1(node root, node cur)
	requires root::thole<s1, p, cur, last> * cur::treep<s2, last> & root != cur & cur != null
	ensures root::thole<s3, p, last, last1> * last::thole<s4, last1, cur, last> * cur::treep<s2, last> 
		& s1 = s3 + s4;
//	ensures root::thole<s3, p, last, last1> * last::treep<s4, last1> & s1 + s2 = s3 + s4;

//lemma "t2th" self::treep<s, p> <- self::thole<s1, p, h, l> * h::treep<s2, l> & s = s1 + s2;

void lemma2(node root)
	requires root::thole<s1, p, h, l> * h::treep<s2, l> & root != null
	ensures root::treep<s, p> & s = s1 + s2 & root != null;


int height(node x)
	requires x::thole<s, p, h, l>
	ensures x::thole<s, p, h, l> & res = s;
	requires x::treep<s, p>
	ensures x::treep<s, p> & res = s;

void plemma2(node root, int s1)
	requires root::thole<s1, p, h, l> * h::treep<s2, l> & root != null
	ensures root::treep<s, p> & s = s1 + s2 & root != null;
{
	if (s1 == 0) {
		unfold root;
		return;
	}
	else {
		assume false;
		return;
	}
}

void up(node root, ref node cur)
	requires root::thole<s1, p, cur, last> * cur::treep<s2, last> & cur != null
	ensures cur'::treep<s, p> & s = s1 + s2 & cur' = root;
{

// assert root != null;

	if (cur != root) {

		lemma1(root, cur);

		cur = cur.parent;

//assert cur' != null;

		lemma2(cur);

//assert cur' != null;

//assert cur'::treep<a,b> * root'::thole<c, d, e, f> & cur' != null;

		up(root, cur);
		return;
	}
	else {
		lemma2(cur);
		return;
	}
}

void f()
{
	node x = new node(0, null, null, null);
	x.left = x;
	x.right = new node(0, null, null, x);
	dprint aa;
}
