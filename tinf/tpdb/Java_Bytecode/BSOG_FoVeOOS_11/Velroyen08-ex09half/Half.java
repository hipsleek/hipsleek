package simple.ex09half;

public class Half {

	/*
	 * This is taken from a broken mergesort, where the calculation of the
	 * borders was wrong. I removed all information about the arrays and so on
	 * an so this is left.
	 */

	public static void loop(int i) {
		int l = i;
		i = 0;
		while (l - i > 0) {
			i = i + (l - i) / 2;
		}
	}
}
