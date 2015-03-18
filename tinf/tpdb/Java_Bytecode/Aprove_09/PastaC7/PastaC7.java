/**
 * Example taken from "A Term Rewriting Approach to the Automated Termination
 * Analysis of Imperative Programs" (http://www.cs.unm.edu/~spf/papers/2009-02.pdf)
 * and converted to Java.
 */

public class PastaC7 {
    public static void main(String[] args) {
        Random.args = args;
        int i = Random.random();
        int j = Random.random();
        int k = Random.random();

        while (i <= 100 && j <= k) {
            int t = i;
            i = j;
            j = i + 1;
            k--;
        }
    }
}
