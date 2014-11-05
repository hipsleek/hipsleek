/**
 * A loop continously throwing and catching an exception.
 * The exception is thrown before the statement that makes the loop
 * progress, but another statement inside the exception catcher make the
 * loop progress. However, this is not enough to prove progression since
 * <tt>i</tt> is decreased at the beginning of the loop.
 *
 * The call to <tt>main()</tt> diverges.
 *
 * Julia + BinTerm cannot prove that the call to <tt>main()</tt> terminates.
 *
 * @author <A HREF="mailto:fausto.spoto@univr.it">Fausto Spoto</A>
 */

public class Exc4 {
    public static void main(String[] args) {
	int i = 0;

	while (i < 20) {
	    i--;

	    try {
		if (i > 10) throw null;
		i += 2;
	    }
	    catch (NullPointerException e) {
		i++;
	    }
	}
    }
}