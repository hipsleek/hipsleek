/**
 * Example taken from "A Term Rewriting Approach to the Automated Termination
 * Analysis of Imperative Programs" (http://www.cs.unm.edu/~spf/papers/2009-02.pdf)
 * and converted to Java.
 */

public class PastaC10 {
    public static void main(String[] args) {
        Random.args = args;
        int i = Random.random();
        int j = Random.random();

        while (i - j >= 1) {
			i = i - Random.random();
			int r = Random.random() + 1;
			j = j + r;
        }
    } 
}
