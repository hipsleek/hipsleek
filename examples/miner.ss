// store list of integers
data node {
	int val;
	node next;
}

data list {
	node l;
	int count;
}

ll<n> == self = null & n = 0
	or self::node<next = r> * r::ll<m> & n = m + 1
	inv n >= 0;

l<n> == self = null & n = 0
	or self::list<count = n, l = r> * r::ll<n>
	inv n >= 0;

// store list of lists of integers
data node2 {
	list val;
	node2 next;
}

ll2<n> == self = null & n = 0
	or self::node2<val = items, next = r> * r::ll2<m> * items::l<ni>
		& n = m + ni
	inv n >= 0;

int length(node l)
	requires l::ll<n>
	ensures l::ll<n> & res = n;
{
	if (l == null) return 0;
	int tmp = 1 + length(l.next);
	return tmp;
}

int length2(list l)
	requires l::l<n>
	ensures l::l<n> & res = n;
{
	if (l == null) return 0;
	return l.count;
}

int calculateSupport(node2 pairs)
	requires pairs::ll2<n>
	ensures pairs::ll2<n> & res = n;
{
	if (pairs == null) return 0;
	int tmp1;
	//tmp1 = length2(pairs.val);
	if (pairs.val == null) {
		tmp1 = 0;
	}
	else {
		tmp1 = pairs.val.count;
	}
	int tmp2 = calculateSupport(pairs.next);
	int tmp3 = tmp1 + tmp2;
	return tmp3;
}


/*
	runtime
*/

int rand_seed(int seed) 
{
	int tmp;
	java {
		tmp = (new java.util.Random(seed)).nextInt();
	}
	return tmp;
}

node create_node(int n, int seed)
	requires n>=0
	ensures res::ll<n>;
{
	if (n <= 0) return null;
	int v = rand_seed(seed);
	node tmp1 = create_node(n - 1, v);
	node tmp2 = new node(v, tmp1);
	return tmp2;
}

node2 create_node2(int n, int seed)
	requires n>=0
	ensures res::ll2<>;
{
	if (n <= 0) 
		return null;

	int seed1 = rand_seed(seed);
//	int n1 = seed1 % 10;
//	if (n1 < 0)
//		n1 = -n1;
//	if (n1 == 0) {
//		n1 = 1;
//		int tmp;
//	}

	int n1 = 10;

	node tmp1 = create_node(n1, seed1);
	node2 tmp2 = create_node2(n - 1, seed1);
	list tmp3 = new list(tmp1, length(tmp1));
	node2 tmp4 = new node2(tmp3, tmp2);
	return tmp4;
}

int test(node2 pairs, int n)
	requires pairs::ll2<m>
	ensures pairs::ll2<m>;
{
	if (n > 0) {
		int sp = calculateSupport(pairs);
		test(pairs, n - 1);
		return sp;
	}
	else return 0;
}

void test1()
{
	int seed = 10;

	java { 
		long time1, time2; 
	}

	node2 pairs;
	int sp;

	pairs = create_node2(1500, seed);
	java { 
		time1 = System.nanoTime(); 
	}
	sp = test(pairs, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("sp = " + sp);
		System.out.println("first time: " + ((time2 - time1) / (double) 1000000));
	}

	pairs = create_node2(500, seed);
	java { 
		time1 = System.nanoTime(); 
	}
	sp =test(pairs, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("sp = " + sp);
		System.out.println("time (500): " + ((time2 - time1) / (double) 1000000));
	}

	pairs = create_node2(1000, seed);
	java { 
		time1 = System.nanoTime(); 
	}
	sp = test(pairs, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("sp = " + sp);
		System.out.println("time (1000): " + ((time2 - time1) / (double) 1000000));
	}

	pairs = create_node2(2000, seed);
	java { 
		time1 = System.nanoTime();
	}
	sp = test(pairs, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("sp = " + sp);
		System.out.println("time (2000): " + ((time2 - time1) / (double) 1000000));
	}

	pairs = create_node2(3000, seed);
	java { 
		time1 = System.nanoTime(); 
	}
	sp = test(pairs, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("sp = " + sp);
		System.out.println("time (3000): " + ((time2 - time1) / (double) 1000000));
	}

	pairs = create_node2(4000, seed);
	java { 
		time1 = System.nanoTime(); 
	}
	sp = test(pairs, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("sp = " + sp);
		System.out.println("time (4000): " + ((time2 - time1) / (double) 1000000));
	}

	pairs = create_node2(5000, seed);
	java { 
		time1 = System.nanoTime(); 
	}
	sp = test(pairs, 10);
	java { 
		time2 = System.nanoTime();
		System.out.println("sp = " + sp);
		System.out.println("time (5000): " + ((time2 - time1) / (double) 1000000));
	}
}

void main() 
{
	test1();
}
