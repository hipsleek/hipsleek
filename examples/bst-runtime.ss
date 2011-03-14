/* trees & binary search trees */

/* representation of a node */
data node {
	int val; 
	node next;	
}

data node2 {
	int val;
	node2 left;
	node2 right; 
}

/* view for trees with number of nodes */
tree1<m> == self = null & m = 0 
	or self::node2<_, p, q> * p::tree1<m1> * q::tree1<m2> & m = 1 + m1 + m2 
	inv m >= 0; 

/* view for trees with number of nodes and depth */
tree<m, n> == self = null & m = 0 & n = 0 
	or self::node2<_, p, q> * p::tree<m1, n1> * q::tree<m2, n2> & m = 1 + m1 + m2 & tmp = max(n1, n2) & n = 1 + tmp
	inv m >= 0 & n >= 0;

/*
tree_1<S> == self = null & S = {}
	or self::node2<v, p, q> * p::tree_1<S1> * q::tree_1<S2> & S = union(S1, S2, {v});
*/

/* function to count the number of nodes in a tree */
int count(node2 z)

	requires z::tree1<m>
	ensures z::tree1<m> & res = m & res >= 0;

{
	int cleft, cright;

	if (z == null)
		return 0;
	else
	{
		cleft = count(z.left);
		cright = count(z.right);
		int tmp = (1 + cleft + cright);
		return tmp;
	}
}

/* binary search trees */

/* view for binary search trees */
bst <sm, lg> == self = null & sm <= lg 
	or self::node2<v, p, q> * p::bst<sm, pl> * q::bst<qs, lg> & pl <= v & qs >= v
	inv sm <= lg;

/*
bst1 <S> == self = null & S = {} 
	or self::node2<v, p, q> * p::bst1<S1> * q::bst1<S2> & S3 = union(S1, S2) & S = union(S3, {v}) 
		& forall (a: (a notin S1 | a<=v)) & forall (b: (b notin S2 | v<=b));
*/

/* insert a node in a bst */
node2 insert(node2 x, int a)
/*
	requires x::bst<sm, lg> 
	ensures res::bst<mi, ma> & res != null & mi = min(sm, a) & ma = max(lg, a);
*/
	requires x::tree<m, n>
	ensures res::tree<m + 1, _>;

{
	node2 tmp;
        node2 tmp_null = null;

	if (x == null) 
	{
		tmp = new node2(a, null, null);
		return tmp;
	}
	else
	{
		if (a <= x.val)
		{
			tmp = x.left;
			x.left = insert(tmp, a);
		}
		else
		{ 
			//tmp = x.right;
			x.right = insert(x.right, a);
		}

		return x;
	} 
}

node2 find(node2 t, int k)
/*
	requires t::bst<sm, lg>
	ensures t::bst<sm, lg>;
*/
	requires t::tree<m, n>
	ensures t::tree<m, n>;
{
	node2 tmp;

	if (t == null) {
		tmp = null;
		return tmp;
	}
	if (t.val == k) return t;
	if (k < t.val) {
		tmp = find(t.left, k);
		return tmp;
	}
	tmp = find(t.right, k);
	return tmp;
}

/*
/* delete a node from a bst */

int remove_min(ref node2 x)

	requires x::bst<s, b> & x != null 
	ensures x'::bst<s1, b> & s <= res <= s1;

{
	int tmp, a; 

	if (x.left == null)
	{
		tmp = x.val;
		x = x.right;

		return tmp; 
	}
	else {
		int tmp2;
/*
		bind x to (_, xleft, _) in { 
			tmp = remove_min(xleft);
		}
*/
		tmp2 = remove_min(x.left);

		return tmp2;
	}
}

void delete(ref node2 x, int a)

	requires x::bst<sm, lg> 
	ensures x'::bst<s, l> & sm <= s & l <= lg;

{
	int tmp; 

	if (x != null)
	{
/*
		bind x to (xval, xleft, xright) in 
		{
			if (xval == a) 
			{
				if (xright == null)
					x = xleft; 
				else
				{
					tmp = remove_min(xright);
					xval = tmp;
				}
			}
			else
			{
				if (xval < a)
					delete(xright, a);
				else
					delete(xleft, a);
			}
		}
*/
			if (x.val == a) 
			{
				if (x.right == null)
					x = x.left; 
				else
				{
					tmp = remove_min(x.right);
					x.val = tmp;
				}
			}
			else
			{
				if (x.val < a)
					delete(x.right, a);
				else
					delete(x.left, a);
			}
		
	}
}
*/


/*
	runtime code
*/

void print_int(int v) {
	java {
		System.out.println("v = " + v);
	}
}

void print_tree(node2 t, int level)
	requires t::tree<>
	ensures t::tree<>;
{
	if (t != null) {
		java {
			for (int i = 0; i < level; i++) 
				System.out.print(" ");
			System.out.println(t.val);
		}
		print_tree(t.left, level + 2);
		print_tree(t.right, level + 2);
	}
}

void print_sep() {
	java {
		System.out.println("==============================================");
	}
}

int rand_seed(int seed) 
{
	int tmp;
	java {
		tmp = (new java.util.Random(seed)).nextInt();
	}
	return tmp;
}

/*
	perform n inserts and n queries, alternatively
*/
node2 test1(node2 t, int n, int seed) 
	requires t::tree<>
	ensures res::tree<>;
{
	if (n > 0) {
		seed = rand_seed(seed);
		t = insert(t, seed);
		// seed = rand_seed(seed);
		node2 tmp = find(t, seed);
		if (tmp.val != seed) {
			java {
				System.out.println("error in test1.");
				System.exit(-1);
			}
		}
		t = test1(t, n - 1, seed);
		return t;
	}
	return t;
}

void run_test1() {
	java { 
		long time1, time2; 
	}
	node2 t;

	java { 
		time1 = System.nanoTime(); 
	}
	t = null;
	t = test1(t, 5, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("first time: " + ((time2 - time1) / (long) 1000000));
	}
	print_sep();
	print_tree(t, 0);
	print_sep();

	java { 
		time1 = System.nanoTime(); 
	}
	t = null;
	test1(t, 500, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (500): " + ((time2 - time1) / (long) 1000000));
	}

	java { 
		time1 = System.nanoTime(); 
	}
	t = null;
	test1(t, 1000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (1000): " + ((time2 - time1) / (long) 1000000));
	}

	java { 
		time1 = System.nanoTime(); 
	}
	t = null;
	test1(t, 2000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (2000): " + ((time2 - time1) / (long) 1000000));
	}

	java { 
		time1 = System.nanoTime(); 
	}
	t = null;
	test1(t, 3000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (3000): " + ((time2 - time1) / (long) 1000000));
	}

	java { 
		time1 = System.nanoTime(); 
	}
	t = null;
	test1(t, 4000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (4000): " + ((time2 - time1) / (long) 1000000));
	}

	java { 
		time1 = System.nanoTime(); 
	}
	t = null;
	test1(t, 5000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (5000): " + ((time2 - time1) / (long) 1000000));
	}
}

void main() {
	run_test1();
}
