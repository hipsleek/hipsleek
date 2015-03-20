/**
 * Example taken from "A Term Rewriting Approach to the Automated Termination
 * Analysis of Imperative Programs" (http://www.cs.unm.edu/~spf/papers/2009-02.pdf)
 * and converted to Java.
 */

public class PastaB8 {
    public static void main(String[] args) {
        Random.args = args;
        int x = Random.random();

        if (x > 0) {
            while (x != 0) {
                if (x % 2 == 0) {
                    x = x/2;
                } else {
                    x--;
                }
            }
        }
    }
}
