/* priority queues */

data node {
	int val;
	int nleft;
	int nright;
	node left;
	node right;
}

data result {
	int val;
	node tree;
}

pq<n, mx> == self = null & n = 0 & mx = 0 
	or self::node<d, n1, n2, l, r> * l::pq<n1, mx1> * r::pq<n2, mx2>
	& n = 1 + n1 + n2 & d >= 0 &  d >= mx1 & d >= mx2 & mx = d & 0 <= n1 - n2 <= 1
	inv n >= 0 & mx >= 0;

/* function to insert an element into a priority queue */
node insert(node t, int v)
	requires t::pq<n, mx> & v >= 0
	ensures res::pq<n1, ma> & n1 = n+1 & ma = max(v, mx); 
{
	node tmp, tmp_null = null; 
	int tmpv;

	if (t == null) {
		tmp = new node(v, 0, 0, tmp_null, tmp_null);
		return tmp;
	}
	else
		if (v > t.val)
		{
			if (t.nleft == t.nright)
			{
				tmp = insert(t.left, t.val);
				t.left = tmp;
				t.nleft++;
			}
			else 
			{	
				tmp = insert(t.right, t.val);
				t.right = tmp; 
				t.nright++;
			}
			t.val = v;
			return t;
		}
		else
		{
			if (t.nleft == t.nright)
			{
				tmp = insert(t.left, v);
				t.left = tmp; 
				t.nleft++;
			}
			else 
			{
				tmp = insert(t.right, v);
				t.right = tmp; 
				t.nright++;
			}
			return t;
		}
}

int get_max(node t)
	requires t::pq<n, mx>
	ensures t::pq<n, mx>;
{
	int tmp = t.val;
	return tmp;
}

/* function to delete the root of a heap tree */
result deletemax(node t)
	
	requires t::pq<n, mx> & t != null
	ensures res::result<val = resv, tree = newt> * newt::pq<n-1, mx2> & mx2 <= resv = mx;

{
	int tmp1;
	int tmp2;

	tmp1 = t.val;

	if (t.nleft == 0) {
		t = null;
	}
	else {
		tmp2 = deleteone(t);
		ripple(tmp2, t);
	}

	result tmp4 = new result(tmp1, t);
	return tmp4;
}

/* function to delete one element */
int deleteone(node t)
	requires t::pq<n, mx>
	ensures t::pq<n - 1, rmx>;
{
	int tmp;
	if (t.nleft > t.nright)
	{
		t.nleft--;
		if (t.nleft == 0) {
			tmp = t.left.val;
			t.left = null;
		}
		else {
			tmp = deleteone(t.left);
		}
		return tmp;
	}
	else 
	{
		t.nright--;
		if (t.nright == 0) {
			tmp = t.right.val;
			t.right = null;
		}
		else {
			tmp = deleteone(t.right);
		}
		return tmp;
	}
}

/* function to restore the heap property */
void ripple(int v, node t)
	requires t::pq<>
	ensures t::pq<>;
{
	node l = t.left;
	node r = t.right;
	if (t.nleft == 0) 
	{
		// parent node is leaf, just store v there
		t.val = v;
	}
	else 
	{
		if (t.nright == 0) 
		{
			// left child is sole child
			if (v >= l.val)
				t.val = v;
			else
			{
				t.val = l.val;
				l.val = v;
			}
		}
		else 
		{
			if (l.val >= r.val)
			{
				if (v >= l.val)
					t.val = v;
				else 
				{
					t.val = l.val;
					ripple(v, t.left);
				}
			}
			else
			{
				if (v >= r.val)
					t.val = v;
				else
				{
					t.val = r.val;
					ripple(v, t.right);
				}
			}
		}
	}
}

/*
	runtime code
*/

void print_int(int v) {
	java {
		System.out.println("v = " + v);
	}
}

void print_tree(node t, int level)
	requires t::pq<>
	ensures t::pq<>;
{
	if (t != null) {
		java {
			System.out.println(t.val);
		}
		if (t.left != null) {
			java {
				for (int i = 0; i < level; i++) 
					System.out.print(" ");
				System.out.print("l ");
			}
			print_tree(t.left, level + 2);
		}
		if (t.right != null) {
			java {
				for (int i = 0; i < level; i++) 
					System.out.print(" ");
				System.out.print("r ");
			}
			print_tree(t.right, level + 2);
		}
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
		tmp = tmp % 20;
	}
	return tmp;
}


node create_tree(int n, int seed)
	requires n >= 0
	ensures res::pq<n, _>;
{
	if (n == 0) return null;
	
	seed = rand_seed(seed);
	if (seed < 0)
		seed = -seed;
	node t = create_tree(n - 1, seed);
	t = insert(t, seed);
	return t;
}

/*
	perform n inserts and n queries, alternatively
*/
node test1(node t, int n, int seed) 
	requires t::pq<>
	ensures res::pq<>;
{
	if (n > 0) {
		seed = rand_seed(seed);
		if (seed < 0)
			seed = -seed;
/*
		print_int(seed);
		print_sep();
		print_tree(t, 2);
*/
		t = insert(t, seed);
/*
		print_sep();
		print_tree(t, 2);
*/
		result re = deletemax(t);
/*
		print_sep();
		print_tree(t, 2);
		print_sep();
*/
		t = test1(re.tree, n - 1, seed);
		return t;
	}
	return t;
}

void run_test0() {
	node t = create_tree(5, 10);
	t = test1(t, 3, 100);
}

void run_test1() {
	java { 
		long time1, time2; 
	}
	node t;

	t = create_tree(1000, 200);
	java { 
		time1 = System.nanoTime(); 
	}
	t = test1(t, 1500, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("first time: " + ((time2 - time1) / (long) 1000000));
	}
//	print_sep();
//	print_tree(t, 2);
//	print_sep();

	t = create_tree(500, 200);
	java { 
		time1 = System.nanoTime(); 
	}
	test1(t, 1000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (500): " + ((time2 - time1) / (long) 1000000));
	}

	t = create_tree(1000, 200);
	java { 
		time1 = System.nanoTime(); 
	}
	test1(t, 1000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (1000): " + ((time2 - time1) / (double) 1000000));
	}

	t = create_tree(2000, 200);
	java { 
		time1 = System.nanoTime(); 
	}
	test1(t, 1000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (2000): " + ((time2 - time1) / (double) 1000000));
	}

	t = create_tree(3000, 200);
	java { 
		time1 = System.nanoTime(); 
	}
	test1(t, 1000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (3000): " + ((time2 - time1) / (double) 1000000));
	}

	t = create_tree(4000, 200);
	java { 
		time1 = System.nanoTime(); 
	}
	test1(t, 1000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (4000): " + ((time2 - time1) / (double) 1000000));
	}

	t = create_tree(5000, 200);
	java { 
		time1 = System.nanoTime(); 
	}
	test1(t, 1000, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("time (5000): " + ((time2 - time1) / (double) 1000000));
	}
}


void main() {
	run_test1();
//	run_test0();
}
