//relation dom(int[] a, int x, int y) == true.

int main()
	requires true
	ensures res = 1;
{
	int[] a;
	assume dom(a', 0, 5);
	a[0] = 1;
	int x = a[0];
	return x;
}
