data dnode {
	int val;
	dnode next;
	dnode prev;
}

/* p: dangling previous pointer, n: size */
dll<p , n> == self = null & n = 0
	or self::dnode<val = v, next = r, prev = p> * r::dll<self, m> & n = m + 1
	inv n >= 0;

sdll<p, n, s> == self = null & n = 0
	or self::dnode<val = s, next = r, prev = p> * r::sdll<self, m, rs> & n = m + 1 & s <= rs //& self != r
	inv n >= 0;

sdsegN<sm, lg, size, p, nex, tail> == self = nex & p = tail & size = 0 & sm = lg
        or self::dnode<val = sm, next = r, prev = p> * r::sdsegN<sm1, lg, size1, self, nex, tail> 
			& self != nex & p != tail
			& size = size1 + 1 
			& sm <= sm1
	inv lg >= sm & size >= 0;

int length(dnode l)
	requires l::dll<p, n>
	ensures l::dll<p, n> & res = n;
{
	if (l == null) return 0;

	l.val = l.val + 1;
	
	int r = 1 + length(l.next);
	return r;
}

dnode insert(dnode l, int v)
	requires l::sdll<p, n, s>
//	ensures res::sdll<_, rn, rs> & rn = n + 1 & (rs = min(s, v) & l != null | rs = v & l = null);
	ensures res::sdll<_, rn, rs> & rn = n + 1 & rs = min(s, v)
		or res::sdll<_, 1, rs> & rs = v & l = null;
//		or rs = v & l = null & rn = 1;
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

/*
dnode insert_n(dnode l, int n, int seed)
	requires l::sdll<p, n, s>
	ensures res::sdll<_, rn, rs> & rn = n + 1;
{
	int vseed = rand_seed(seed);
	if (l == null) {
		dnode tmp = new dnode(vseed, null, null);
		return tmp;
	}
	else if (v < l.val) {
		dnode tmp = new dnode(vseed, l, null);
		l.prev = tmp;
		return tmp;
	}
	else {
		dnode tmp = insert_n(l.next, n - 1, vseed);
		l.next = tmp;
		tmp.prev = l;
		return l;
	}
}
*/


dnode insert2(dnode l, dnode v)
	requires l::sdll<p, n, s> * v::dnode<val = vv, next = vn, prev = vp>

//	ensures res::sdll<_, rn, rs> & rn = n + 1 & (rs = min(s, vv) & l != null | rs = vv & l = null);

	ensures res::sdll<_, rn, rs> & rn = n + 1 & l != null & rs = min(s, vv)
		or res::sdll<_, 1, rs> & rs = vv & l = null;

{
	if (l == null) {
		v.next = null;
		v.prev = null;
		return v;
	}
	else if (v.val < l.val) {
		v.next = l;
		l.prev = v;
		return v;
	}
	else {
		dnode tmp = insert2(l.next, v);
		l.next = tmp;
		tmp.prev = l;
		return l;
	}
}

dnode sort(dnode l)
	requires l::dll<p, n>
	ensures res::sdll<_, n, _>;
{
	if (l != null) {
		dnode tmp = sort(l.next);
		tmp = insert2(tmp, l);
		return tmp;
	}
	return l;
}


dnode search_top_k(dnode l, int k)
	requires l::sdll<p, s, sm> & l != null & k >= 0
//	ensures true;
//	ensures l::sdsegN<> * res::sdll<>;
	ensures l::sdsegN<sm, lg, s1, p, n1, t> * res::sdll<t, s2, sm2>
		& s = s1 + s2 & lg <= sm2 & n1 = res;
{
	if (k == 0) {
		dnode tmp = l.prev;
		return l.prev;
	}

	if (l.next != null) {
		dnode tmp = search_top_k(l.next, k - 1);
		return tmp;
	}

	return l;
}


void print_int(int v) {
	java {
		System.out.println("v = " + v);
	}
}

void print_sep() {
	java {
		System.out.println("==============================================");
	}
}

void print_all(dnode l)
	requires l::dll<p, n>
	ensures l::dll<p, n>;
{
	if (l != null) {
		print_int(l.val);
		print_all(l.next);
	}
}

void print_rev(dnode l)
{
	if (l != null) {
		print_int(l.val);
		print_rev(l.prev);
	}
}

dnode create(int n, int i) 
	requires n >= 0
	ensures res::dll<p, n>	;
{
	if (n <= 0) return null;
	
	dnode tmp1 = new dnode(i, null, null);
	dnode tmp2 = create(n - 1, i + 1);
	tmp1.next = tmp2;
	if (tmp2 != null)
		tmp2.prev = tmp1;
	return tmp1;
}

int rand() {
	int tmp;
	java {
		tmp = (int)(((double) 10000) * Math.random());
	}
	return tmp;
}

int rand_seed(int seed) 
{
	int tmp;
	java {
		tmp = (new java.util.Random(seed)).nextInt();
	}
	return tmp;
}

dnode create_seed(int n, int seed)
	requires n >= 0
	ensures res::dll<p, n>;
{
	if (n <= 0) return null;
	
	int vseed = rand_seed(seed);
	dnode tmp1 = new dnode(vseed, null, null);
	dnode tmp2 = create_seed(n - 1, vseed);
	tmp1.next = tmp2;
	if (tmp2 != null)
		tmp2.prev = tmp1;
	return tmp1;
}

dnode create_rand(int n)
	requires n >= 0
	ensures res::dll<p, n>	;
{
	if (n <= 0) return null;
	
	dnode tmp1 = new dnode(rand(), null, null);
	dnode tmp2 = create_rand(n - 1);
	tmp1.next = tmp2;
	if (tmp2 != null)
		tmp2.prev = tmp1;
	return tmp1;
}


dnode test0(dnode l, int n)
	requires l::sdll<>
	ensures res::sdll<>;
{
	if (n >= 0) {
		dnode tmp = insert(l, rand());
		tmp = test0(tmp, n - 1);
		return tmp;
	}
	return l;
}

void run_test0()
{
	java {
		long time1 = System.nanoTime();
	}
	dnode l = null;
	l = test0(l, 40);
	int n = length(l);
	print_int(n);
	java {
		long time2 = System.nanoTime();
		System.out.println("time: " + ((time2 - time1) / (long)1000000));
	}
}

// test sort
void test1()
{
	java { 
		long time1, time2; 
		// long mem1, mem2;
	}

	dnode l;

	l = create_seed(1000, 10);
	java { 
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("first time: " + ((time2 - time1) / (long) 1000000));
	}

/*
	l = create_seed(10, 1);
	java { 
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	print_all(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (10): " + ((time2 - time1) / (long) 1000000));
	}

	l = create_seed(50, 1);
	java { 
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (50): " + ((time2 - time1) / (long) 1000000));
	}

	l = create_seed(100, 1);
	java { 
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (100): " + ((time2 - time1) / (long) 1000000));
	}
*/

	l = create_seed(500, 10);
	java {
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (500): " + ((time2 - time1) / (long) 1000000));	
	}

	l = create_seed(1000, 10);
	java {
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (1000): " + ((time2 - time1) / (long) 1000000));	
	}

	l = create_seed(2000, 10);
	java {
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (2000): " + ((time2 - time1) / (long) 1000000));	
	}

	l = create_seed(3000, 1);
	java {
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (3000): " + ((time2 - time1) / (long) 1000000));	
	}

	l = create_seed(4000, 1);
	java {
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (4000): " + ((time2 - time1) / (long) 1000000));	
	}

	l = create_seed(5000, 1);
	java {
		time1 = System.nanoTime(); 
	}
	l = sort(l);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (5000): " + ((time2 - time1) / (long) 1000000));	

//		Runtime.getRuntime().gc();
//		mem2 = Runtime.getRuntime().totalMemory();
//		System.out.println("mem: " + (mem2));
	}


//	print_all(l);
//	print_sep();
//	if (n > 0) 
//		test1(n - 1);
}

void main() 
{

	test1();

//	run_test0();
//	int n;

//	dnode l = create_seed(10, 4);
//	print_all(l);

//	dnode l = create_rand(10);
//	print_all(l);
//	print_sep();
//	l = sort(l);
//	print_all(l);

	int tmp;
}

/*
void main() {
	dnode l = create(3, 1);
	l = insert(l, 3);
	l = insert(l, 10);
	l = insert(l, 4);
	l = insert(l, -1);
	print_all(l);
	print_sep();
	int n = length(l);
	print_int(n);
	print_sep();
	dnode tmp = search_top_k(l, 2);
	print_all(tmp);
}
*/
