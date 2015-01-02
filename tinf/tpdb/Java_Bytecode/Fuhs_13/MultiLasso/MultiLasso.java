/**
 * All lasso-shaped runs of this program are terminating.
 */
public class MultiLasso {
    
    public static void main(String[] args) {
        int x = args[0].length() - args[1].length();
        int y;

        while (x > 0) {
            x++;
            y = x;
            while (y > 0) {
                y--;
            }
        }
    }
}
