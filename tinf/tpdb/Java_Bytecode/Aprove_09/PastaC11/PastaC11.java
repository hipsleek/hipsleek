/**
 * Example taken from "A Term Rewriting Approach to the Automated Termination
 * Analysis of Imperative Programs" (http://www.cs.unm.edu/~spf/papers/2009-02.pdf)
 * and converted to Java.
 */

public class PastaC11 {
    public static void main(String[] args) {
        Random.args = args;
        int x = Random.random();
        int y = Random.random();

        while (true) {
			if (x >= 0) {
				x--;
				y = Random.random();
			} else if (y >= 0) {
				y--;
			} else {
				break;
			}
        }
    } 
}
