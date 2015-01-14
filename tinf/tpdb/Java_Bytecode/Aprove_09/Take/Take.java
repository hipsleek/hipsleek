/**
 * Java can do infinite data objects, too.
 * Here we take the first n elements from an
 * ascending infinite list of integer numbers.
 *
 * @author Carsten Fuhs
 */
public class Take {

    public static int[] take(int n, MyIterator f) {
        int[] result = new int[n];
        for (int i = 0; i < n; ++i) {
            if (f.hasNext()) {
                result[i] = f.next();
            }
            else {
                break;
            }
        }
        return result;
    }

    public static void main(String args[]) {
        int start = args[0].length();
        int howMany = args[1].length();
        From f = new From(start);
        int[] firstHowMany = take(howMany, f);
    }
}

interface MyIterator {
    boolean hasNext();
    int next();
}

class From implements MyIterator {

    private int current;

    public From(int start) {
        this.current = start;
    }

    public boolean hasNext() {
        return true;
    }

    public int next() {
        return current++;
    }
}

