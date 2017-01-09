package simple.whileSum;

public class WhileSum {

	public static void increase(int i, int j) {
		while (i+j > 0) {
			i++;
			if (j % 2 == 0) {
				j = j - 2;
			}
		}
	}
}
