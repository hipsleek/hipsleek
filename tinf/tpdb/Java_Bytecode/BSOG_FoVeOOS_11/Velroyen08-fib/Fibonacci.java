package simple.fib;

public class Fibonacci {

	public static void fib(int n) {
		int i = 0;
		int j = 1;
		int t = 0;
		while (j != n) {
			t = j+i;
			i = j;
			j = t;
		}
	}
}
