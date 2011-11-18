data dnode {
	int val;
	dnode next;
	dnode prev;
}

/* p: dangling previous pointer, n: size */
dll<p , n> == self = null & n = 0
	or self::dnode<val = v, next = r, prev = p> * r::dll<self, m> & n = m + 1
	inv n >= 0;

dll2<p, n> == self::dnode<_, null, p> & n = 1
	or self::dnode<next = r, prev = p> * r::dll2<self, m> & n = m + 1 & r != null
	inv n >= 1 & self != null;

/* p, n: same as above, s: smallest element */
sdll<p, n, s> == self = null & n = 0
	or self::dnode<val = s, next = r, prev = p> * r::sdll<self, m, rs> & n = m + 1 & s <= rs //& self != r
	inv n >= 0;

sdll2<p, n, s> == self::dnode<val = s, next = null, prev = p> & n = 1
	or self::dnode<val = s, next = r, prev = p> * r::sdll2<self, m, rs> & n = m + 1 & s <= rs
	inv n >= 1;

dsegN<s, p, n @ in, t> == self = n & p = t & s = 0
    or self::dnode<next = r, prev = p> * r::dsegN<s1, self, n, t> & self != n & p != t & s = s1 + 1
	inv s >= 0;


sdsegN<sm, lg, size, prev, next, tail> == self = next & prev = tail & size = 0 & sm = lg
        or self::dnode<val = sm, next = r, prev = prev> * r::sdsegN<sm1, lg, size1, self, next, tail> 
			& self != next & prev != tail
			& size = size1 + 1 
			& sm <= sm1
	inv lg >= sm & size >= 0;

/*
lemma self::sdsegN<sm, lg, size, prev, next, tail> & size > 0 <->
	self::sdsegN<sm, lg1, size1, prev, next1, tail1> * tail::dnode<val = v, prev = tail1, next = next> 
		& next1 = tail & size = size1 + 1
		& lg1 <= v;
*/
	
/* Functions */

dnode search_top_k(dnode l, int k)
	requires l::sdll<p, n, sm> & l != null & k >= 0
	ensures l::sdsegN<sm, lg, n1, p, res, t> * res::sdll<t, n2, sm2>
		& n = n1 + n2 & lg <= sm2;
{
	if (k == 0) {
		dnode tmp = l.prev;
/*
	How do I know that p is either null, or points to a node
	unfolded by previous calls?

	I need some global information about this.
*/
assert tmp'::dnode<>;
assert tmp'::sdll<>;
assume false;
		return l.prev;
	}

	if (l.next != null) {
		dnode tmp = search_top_k(l.next, k - 1);
		return tmp;
	}

	return l;
}

void print_top_k(dnode l, int k)
	requires l::sdll<p, n, s>
	ensures l::sdll<p, n, s>;
{
	if (l != null) {
		dnode tmp = search_top_k(l, k);
		print_rev(tmp);
	}
}

void print_rev(dnode l)
{
	if (l != null) {
		print(l.val);
		print_rev(l.prev);
	}
}

void append(dnode x, dnode n, dnode y, dnode yn)
	requires x::dsegN<s, p, n, t> * y::dsegN<n = yn> & x != n
	ensures x::dsegN<n = _> ;
	requires x::sdsegN<sm = xsm, lg = xlg, next = xn> * y::sdsegN<sm = ysm, next = yn> & x != xn & xlg <= ysm
	ensures x::sdsegN<>;
{
	if (x.next == n)
		x.next = y;
	else {
		dnode tmp = x.next;
assert tmp' != n;
		append(tmp, n, y, yn);
	}
}

dnode insert(dnode l, int v)
	requires l::sdll<p, n, s>
	ensures res::sdll<_, rn, rs> & rn = n + 1 & (rs = min(s, v) & l != null | rs = v & l = null);
{
	if (l == null) {
		dnode tmp = new dnode(v, null, null);
		return tmp;
	}
	else if (v < l.val) {
		dnode tmp = new dnode(v, l, null);
		l.prev = tmp;
		return tmp;
	}
	else {
		dnode tmp = insert(l.next, v);
		l.next = tmp;
		tmp.prev = l;
		return l;
	}
}

void print_all(dnode l)
{
	if (l != null) {
		print(l.val);
		print_all(l.next);
	}
}

void print(int v) {
	java {
		System.out.println("v = " + v);
	}
}

int length(dnode l)
//	requires l::dll<p, n>
//	ensures l::dll<p, n> & res = n;

	requires l::dll2<p, n> 
			or l = null
	ensures l::dll2<p, n> & res = n
			or l = null & res = 0;
{
	if (l == null) return 0;
	int r = 1 + length(l.next);
	return r;
}

void test() 
{
	dnode l = null;
	int i = length(l);

	dnode l2 = new dnode(0, null, null);
	int j = length(l2);

	//dnode l3 = new dnode(1, l2, null);
	//l2.prev = l3;
	//int k = length(l3);
	//assert i = 0 & j = 1 & k = 1;
}

dnode create(int n) {
	if (n <= 0) return null;
	
	dnode tmp1 = new dnode(n, null, null);
	dnode tmp2 = create(n - 1);
	tmp1.next = tmp2;
	if (tmp2 != null)
		tmp2.prev = tmp1;
	return tmp1;
}

void main() {
	dnode l = create(5);

	print_all(l);

	int k = 4;
//	print_top_k(l, k);
}