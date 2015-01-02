/**
 * Example taken from "A Term Rewriting Approach to the Automated Termination
 * Analysis of Imperative Programs" (http://www.cs.unm.edu/~spf/papers/2009-02.pdf)
 * and converted to Java.
 */

public class PastaB13 {
    public static void main(String[] args) {
        Random.args = args;
        int x = Random.random();
        int y = Random.random();
        int z = Random.random();

        while (x > z || y > z) {
            if (x > z) {
                x--;
            } else if (y > z) {
                y--;
            } else {
                continue;
            }
        }
    }
}
