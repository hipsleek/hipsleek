data node {
	int val1;
	bool val2;
	node next;
}

ll1<n> == self=null & n=0
	or self::node<iv, bv, r> * r::ll1<n-1> inv n>=0;

/*
int id(int x) requires x>0 ensures x>0 {
	int a = x;
	return a;
}
*/

/*
void test() requires true ensures true {
	int a;
	int b = a;
	a = 10;
	return;
}
*/

//void test2

int test1(int x) 
	requires x>0 ensures res<0
{
	return x;
}
