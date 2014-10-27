/**
 * Parts of the below code have been adapted from
 *
 * http://www0.cs.ucl.ac.uk/staff/p.ohearn/Talks/SAStalk.pdf
 *
 * Based on the motivating example of the paper
 *
 * Automatic termination proofs for programs with shape-shifting heaps
 * Josh Berdine, Byron Cook, Dino Distefano, and Peter W. O’Hearn
 * In Proc. CAV'06, LNCS 4144, pp. 386 - 400, 2006.
 */
public class Kernel88 {
    /**
     * A reference to the next list element.
     */
    private Kernel88 next;
    
    public static void main(String[] args) {
        int random1 = args[0].length();
        int random2 = args[1].length();

        //slide68(random1, random2);
        slide88(random1, random2);
        //slide93(random1, random2);
        //slide95(random1, random2);
    }
    
    /**
     * Create a new list element.
     * @param n a reference to the next element.
     */
    public Kernel88(final Kernel88 n) {
        this.next = n;
    }
    
    /**
     * Create a new cyclical list of a length x.
     * @param x some length
     * @return cyclical list of length max(1, x)
     */
    public static Kernel88 create(int x) {
        Kernel88 last, current;
        last = current = new Kernel88(null);
        while (--x > 0)
            current = new Kernel88(current);
        return last.next = current;
    }

    /**
     * Check if the last bit of x is &gt; 0.
     */
    private static boolean check(int x) {
        return x % 2 > 0;
    }

    public static void slide68(int random1, int random2) {
        Kernel88 h = create(random1);
        Kernel88 p = h;
        Kernel88 c = p.next;
        while (c != h) {
            Kernel88 o = c;
            c = c.next;
            if (check(random2)) { // nondet()
                p.next = c;
                //dispose(o);
                o = null;
                // Java's garbage collector will notice that the object
                // previously referenced by o is not referenced any more
                // and will release it (of course, in the next loop iteration
                // this would happen anyway); obviously, this does not have
                // quite the impact of a proper "dispose" operation, which
                // also renders all other pointer invalid that happen to point
                // to the same address
            } else {
                p = o;
            }

            // get a fresh random bit to the end of random2
            random2 = random2 / 2;
       }
    }

    public static void slide88(int random1, int random2) {
        Kernel88 h = create(random1);
        Kernel88 p = h;
        Kernel88 c = p.next;
        while (c != h) {
            Kernel88 o = c;
            //c = c.next;
            if (check(random2)) { // nondet()
                Kernel88 e = o.next;
                p.next = e;
                //dispose(o);
                o = null;
                // Java's garbage collector will notice that the object
                // previously referenced by o is not referenced any more
                // and will release it
                c = o;
                // for a faithful translation of the original C code,
                // let c point to whatever o points to -- the interesting
                // aspect is that dereferencing this memory location 
                // henceforth is a very bad idea (in C, obviously, this would
                // not necessarily lead to a clean exception at runtime)
            } else {
                p = o;
            }
            c = c.next;

            // get a fresh random bit to the end of random2
            random2 = random2 / 2;
        }
    }

    /**
     * Non-terminating.
     */
    public static void slide93(int random1, int random2) {
        Kernel88 h = create(random1);
        Kernel88 p = h;
        Kernel88 c = p.next;
        while (c != h) {
            Kernel88 o = c;
            //c = c.next;

            if (check(random2)) { // nondet()
                Kernel88 e = o.next;
                p.next = e;
                o.next = o;
            } else {
                p = o;
            }
            c = c.next;

            // get a fresh random bit to the end of random2
            random2 = random2 / 2;
        }
    }

    public static void slide95(int random1, int random2) {
        Kernel88 h = create(random1);
        Kernel88 p = h;
        Kernel88 c = p.next;
        while (c != h) {
            Kernel88 o = c;
            c = c.next;

            if (check(random2)) { // nondet()
                Kernel88 e = o.next;
                p.next = e;
                o.next = o;
            } else {
                p = o;
            }

            // get a fresh random bit to the end of random2
            random2 = random2 / 2;
        }
    }

}
