data node {
	int val;
	node next;
}


void test_uop() {
	int a, b, c;
	node node1, node2;

	a++;
	a--;
	++c;
	--c;
	b = a++;
	b = --c;
	b = a++ + --c;
}
