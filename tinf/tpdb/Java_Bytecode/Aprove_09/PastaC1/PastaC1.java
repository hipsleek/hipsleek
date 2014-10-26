/**
 * Example taken from "A Term Rewriting Approach to the Automated Termination
 * Analysis of Imperative Programs" (http://www.cs.unm.edu/~spf/papers/2009-02.pdf)
 * and converted to Java.
 */

public class PastaC1 {
    public static void main(String[] args) {
        Random.args = args;
        int x = Random.random();

		while (x >= 0) {
			int y = 1;
			while (x > y) {
				y = 2*y;
			}
			x--;
		}
    }
}
