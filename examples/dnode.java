class dnode {
	long color;
	int val;
	dnode next;
	dnode prev;

	static void print_less_k(dnode d, int k) 
	//		requires d::sdll2<p, n, s>
	//		ensures d::sdll2<p, n, s>;
	{
		dnode tmp = d; // d, tmp != null

		// search for pointer
		while (tmp.next != null && tmp.val < k)
			tmp = tmp.next;

		// move back one step
		tmp = tmp.prev;

		while (tmp != null) {
			System.out.println("val = " + tmp.val);
			tmp = tmp.prev;
		}
	}
}

