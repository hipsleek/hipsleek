data node {
	int val;
	node next;
}

data test_data {
	bool value;
}

int test_call2() {
	dummy();
	return 1;
}

int test_call3() {
	if (true) {
		int tmp;
		dummy();
		test_call3();
		return tmp;
	}
	else 
		dummy();
	return 1;
	
}


node test_call1(int a, node b) {
	node node1, tmp=null;

	test_call1(a, b).next = tmp;

	test_call1(a, b.next).next.next.val = 10;

	tmp = test_call1(node1.next.val, b.next).next;

	tmp.next = node1.next;

	node tmp2 = tmp.next;


	return b;
}

int id(int x) {
        dummy();
	return x;
}

int dummy() {
	return 1;
}

