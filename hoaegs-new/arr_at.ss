//relation dom(int[] a, int x, int y) == true.

relation test(int[] a, int[] b, int n) ==
	forall(i : i < 1 | i > n | a[i] <= b[i]).

int[] h(int[] a) {
	//int[] x;
	return a;
}

int main()
	//requires true
	//ensures res = 1;
{
	int x = 1;
	int[] a;
	//assume dom(a', 0, 5);
	//a[0] = 1;
	//int x = a[0];
	return x;
}
