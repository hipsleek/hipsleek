/**
 * Example taken from "A Term Rewriting Approach to the Automated Termination
 * Analysis of Imperative Programs" (http://www.cs.unm.edu/~spf/papers/2009-02.pdf)
 * and converted to Java.
 */

public class PastaC5 {
    public static void main(String[] args) {
        Random.args = args;
        int x = Random.random();
        int y = Random.random();

        if (x > 0 && y > 0) {
            while (x != y) {
                if (x > y) {
                    x = x - y;
                } else {
                    y = y - x;
                }
            }
        }
    }
}
