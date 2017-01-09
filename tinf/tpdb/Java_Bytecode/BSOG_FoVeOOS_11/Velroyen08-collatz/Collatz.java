package simple.collatz;

public class Collatz {

	public static void collatz(int i) {
		while (i > 1) {
			if (i % 2 == 0) {
				i = i/2;
			} else {
				i = 3*i+1;
			}
		}
	}
}
