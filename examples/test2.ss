data node {
	int val;
	node next;
}

data test_data {
	bool value;
}

void test_member_access(int d) {
	node tmp, node1;
	int tmp1;

	tmp.val = d;

	tmp.next = tmp;

	tmp.next.next.val = 10;

	d = tmp.val;
	tmp = tmp.next.next;
	tmp = ((tmp.next).next).next;
	tmp1 = tmp.next.next.next.val;
}

int test_if(test_data p) {
	if (p.value) {
		return 1;
	}
	else return 2;
}

bool test_alpha_naming() {
	int a, b = 10;
	bool c;

	if (c) {
		bool b;
		//bool b__alpha__1; how about name clashes between alpha-names and user-names?
		int d;

		b = true;
		return b;
	}
	else {
		bool c;
		return c;
	}
}
