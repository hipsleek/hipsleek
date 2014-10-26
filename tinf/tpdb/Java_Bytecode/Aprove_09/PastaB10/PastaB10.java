/**
 * Example taken from "A Term Rewriting Approach to the Automated Termination
 * Analysis of Imperative Programs" (http://www.cs.unm.edu/~spf/papers/2009-02.pdf)
 * and converted to Java.
 */

public class PastaB10 {
    public static void main(String[] args) {
        Random.args = args;
        int x = Random.random();
        int y = Random.random();

        while (x + y > 0) {
            if (x > 0) {
                x--;
            } else if (y > 0) {
                y--;
            } else {
                continue;
            }            
        }
    }
}
